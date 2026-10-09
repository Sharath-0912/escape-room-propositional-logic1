"""
AI Escape Room — Propositional Logic
Run with: pip install flask && python main.py
Everything (Flask, logic engine, UI, game data) lives in this file.
"""
import itertools
import os
import re
import time
from flask import Flask, jsonify, render_template_string, request, session

app = Flask(__name__)
app.secret_key = os.urandom(32)
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax")

CORRECT, WRONG, HINT, ROOM_BONUS, ESCAPE_BONUS = 100, -20, -25, 150, 500
START_LIVES = 3


# -------------------- Safe propositional logic parser --------------------
TOKEN_RE = re.compile(
    r"\s*(<->|->|→|[()¬~!∧&^∨|]|AND\b|OR\b|NOT\b|IMPLIES\b|TRUE\b|FALSE\b|[A-Za-z][A-Za-z0-9_]*)",
    re.I,
)


class LogicError(ValueError):
    pass


def logical_and(a, b):
    return bool(a and b)


def logical_or(a, b):
    return bool(a or b)


def logical_not(a):
    return not a


def implies(a, b):
    return (not a) or b


class Parser:
    """Recursive descent parser. Never evaluates Python or arbitrary input."""
    def __init__(self, text):
        if not isinstance(text, str) or not text.strip():
            raise LogicError("Enter a logical expression.")
        if len(text) > 160:
            raise LogicError("Expressions are limited to 160 characters.")
        self.tokens = []
        pos = 0
        while pos < len(text):
            m = TOKEN_RE.match(text, pos)
            if not m:
                if text[pos:].strip():
                    raise LogicError(f"Unsupported character near {text[pos:pos+12]!r}.")
                break
            raw = m.group(1)
            pos = m.end()
            upper = raw.upper()
            if upper == "AND" or raw in ("&", "^", "∧"):
                token = "AND"
            elif upper == "OR" or raw in ("|", "∨"):
                token = "OR"
            elif upper == "NOT" or raw in ("¬", "~", "!"):
                token = "NOT"
            elif upper == "IMPLIES" or raw in ("->", "→"):
                token = "IMPLIES"
            elif raw == "<->":
                token = "IFF"
            elif upper in ("TRUE", "FALSE"):
                token = upper
            else:
                token = upper
            self.tokens.append(token)
        self.i = 0

    def peek(self):
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None:
            raise LogicError("The expression ends unexpectedly.")
        if expected and token != expected:
            raise LogicError(f"Expected {expected}, found {token}.")
        self.i += 1
        return token

    def parse(self):
        tree = self.iff()
        if self.peek() is not None:
            raise LogicError(f"Unexpected token {self.peek()}.")
        return tree

    def iff(self):
        node = self.implication()
        while self.peek() == "IFF":
            self.take()
            node = ("iff", node, self.implication())
        return node

    def implication(self):
        left = self.disjunction()
        if self.peek() == "IMPLIES":
            self.take()
            return ("implies", left, self.implication())
        return left

    def disjunction(self):
        node = self.conjunction()
        while self.peek() == "OR":
            self.take()
            node = ("or", node, self.conjunction())
        return node

    def conjunction(self):
        node = self.unary()
        while self.peek() == "AND":
            self.take()
            node = ("and", node, self.unary())
        return node

    def unary(self):
        token = self.peek()
        if token == "NOT":
            self.take()
            return ("not", self.unary())
        if token == "(":
            self.take("(")
            node = self.iff()
            self.take(")")
            return node
        if token is None or token in ("AND", "OR", "IMPLIES", "IFF", ")"):
            raise LogicError("Expected a proposition or parenthesized expression.")
        self.take()
        if token == "TRUE":
            return ("constant", True)
        if token == "FALSE":
            return ("constant", False)
        return ("variable", token)


def eval_tree(tree, values):
    op = tree[0]
    if op == "constant":
        return tree[1]
    if op == "variable":
        if tree[1] not in values:
            raise LogicError(f"No truth value was supplied for {tree[1]}.")
        return bool(values[tree[1]])
    if op == "not":
        return logical_not(eval_tree(tree[1], values))
    a, b = eval_tree(tree[1], values), eval_tree(tree[2], values)
    return {
        "and": logical_and,
        "or": logical_or,
        "implies": implies,
        "iff": lambda left, right: left == right,
    }[op](a, b)


def variables(tree):
    found = set()
    def visit(node):
        if node[0] == "variable":
            found.add(node[1])
        elif node[0] == "not":
            visit(node[1])
        elif node[0] in ("and", "or", "implies", "iff"):
            visit(node[1])
            visit(node[2])
    visit(tree)
    return sorted(found)


def eval_expression(expression, values):
    return eval_tree(Parser(expression).parse(), values)


def truth_table(expression):
    tree = Parser(expression).parse()
    names = variables(tree)
    if len(names) > 8:
        raise LogicError("Truth tables are limited to eight propositions.")
    rows = []
    for combination in itertools.product((True, False), repeat=len(names)):
        assignment = dict(zip(names, combination))
        rows.append({"values": assignment, "result": eval_tree(tree, assignment)})
    results = [row["result"] for row in rows]
    classification = "TAUTOLOGY" if all(results) else (
        "CONTRADICTION" if not any(results) else "CONTINGENCY"
    )
    return {
        "expression": expression,
        "variables": names,
        "rows": rows,
        "classification": classification,
        "satisfiable": any(results),
    }


# -------------------- Knowledge base / forward chaining --------------------
def forward_chain(facts, rules):
    known, chain = {fact.upper() for fact in facts}, []
    changed = True
    while changed:
        changed = False
        for rule in rules:
            premises = [value.upper() for value in rule["if"]]
            conclusion = rule["then"].upper()
            if all(p in known for p in premises) and conclusion not in known:
                known.add(conclusion)
                chain.append({"premises": premises, "conclusion": conclusion})
                changed = True
    return known, chain


# -------------------- Fifteen puzzles: three in each of five rooms --------------------
ROOMS = [
    {"id": 1, "name": "The Locked Door", "tag": "SIGNAL DECK", "accent": "cyan"},
    {"id": 2, "name": "Security Lab", "tag": "ACCESS CONTROL", "accent": "blue"},
    {"id": 3, "name": "AI Vault", "tag": "KNOWLEDGE BASE", "accent": "violet"},
    {"id": 4, "name": "Logic Chamber", "tag": "TRUTH ANALYSIS", "accent": "green"},
    {"id": 5, "name": "AI Core", "tag": "CORE OVERRIDE", "accent": "red"},
]

PUZZLES = [
    {"room":1,"kind":"evaluate","title":"Dual-switch gate","prompt":"The door opens only when both switches are active.","expression":"P ∧ Q","facts":{"P":True,"Q":False},"labels":{"P":"Red switch is ON","Q":"Blue switch is ON"},"hint":"AND is true only when every proposition on both sides is true."},
    {"room":1,"kind":"evaluate","title":"Backup power","prompt":"At least one independent power source must be online.","expression":"P ∨ Q","facts":{"P":False,"Q":True},"labels":{"P":"Main power is online","Q":"Backup power is online"},"hint":"OR is true when at least one proposition is true."},
    {"room":1,"kind":"evaluate","title":"Silent alarm","prompt":"The alarm is disabled when the sensor is not active.","expression":"¬P","facts":{"P":True},"labels":{"P":"Motion sensor is active"},"hint":"NOT reverses a proposition's truth value."},
    {"room":2,"kind":"infer_boolean","title":"Badge authorization","prompt":"The badge is verified. Does the system derive that the door unlocks?","facts":["BADGE"],"rules":[{"if":["BADGE"],"then":"DOOR"},{"if":["DOOR"],"then":"CORRIDOR"}],"target":"DOOR","hint":"With P → Q and P known true, Modus Ponens derives Q."},
    {"room":2,"kind":"infer_boolean","title":"Thermal override","prompt":"The cooling system is offline. Can the alarm proposition be derived?","facts":["COOLING_OFF"],"rules":[{"if":["COOLING_OFF"],"then":"ALARM"}],"target":"ALARM","hint":"A rule fires only when all of its premises are known facts."},
    {"room":2,"kind":"infer_boolean","title":"Two-factor checkpoint","prompt":"The code is valid and the badge is present. Is access granted?","facts":["CODE_VALID","BADGE_PRESENT"],"rules":[{"if":["CODE_VALID","BADGE_PRESENT"],"then":"ACCESS"}],"target":"ACCESS","hint":"This rule has two premises; both must be known."},
    {"room":3,"kind":"infer_boolean","title":"Research wing","prompt":"Can the lab rules establish that the archive is open?","facts":["SCIENTIST","CLEARANCE"],"rules":[{"if":["SCIENTIST"],"then":"LAB_ACCESS"},{"if":["CLEARANCE"],"then":"VAULT_KEY"},{"if":["LAB_ACCESS","VAULT_KEY"],"then":"ARCHIVE_OPEN"}],"target":"ARCHIVE_OPEN","hint":"Forward chaining repeatedly applies rules whose premises are known."},
    {"room":3,"kind":"infer_boolean","title":"Containment protocol","prompt":"A fault is detected, but no isolation signal is known. Is containment confirmed?","facts":["FAULT"],"rules":[{"if":["FAULT","ISOLATION"],"then":"CONTAINED"}],"target":"CONTAINED","hint":"A missing premise blocks a rule even if its other premise is true."},
    {"room":3,"kind":"infer_boolean","title":"Power restoration","prompt":"The generator is running. Follow the rules: is the elevator powered?","facts":["GENERATOR"],"rules":[{"if":["GENERATOR"],"then":"GRID_ON"},{"if":["GRID_ON"],"then":"ELEVATOR_POWERED"}],"target":"ELEVATOR_POWERED","hint":"Keep applying rules after the first new fact; derived facts can fire other rules."},
    {"room":4,"kind":"classify","title":"Contradictory sensor","prompt":"Classify this formula by checking every possible truth assignment.","expression":"P ∧ ¬P","hint":"A contradiction is false on every row of its truth table."},
    {"room":4,"kind":"classify","title":"Logical certainty","prompt":"Is this formula true under every possible assignment?","expression":"P ∨ ¬P","hint":"A tautology is true on every row, whatever P's value is."},
    {"room":4,"kind":"classify","title":"Conditional evidence","prompt":"Some assignments make this formula true and others false. Name its classification.","expression":"P ∧ Q","hint":"A contingency is satisfiable but not true on every row."},
    {"room":5,"kind":"derive","title":"Core signal","prompt":"Enter the proposition derived from the active core rules.","facts":["P","Q"],"rules":[{"if":["P"],"then":"R"},{"if":["Q"],"then":"S"},{"if":["R","S"],"then":"T"},{"if":["T"],"then":"U"}],"target":"R","hint":"Start with P and Q, then apply rules whose inputs are known."},
    {"room":5,"kind":"derive","title":"Core convergence","prompt":"Combine the two derived branches. Enter the proposition they establish.","facts":["P","Q"],"rules":[{"if":["P"],"then":"R"},{"if":["Q"],"then":"S"},{"if":["R","S"],"then":"T"},{"if":["T"],"then":"U"}],"target":"T","hint":"The rule for T needs both R and S; derive each branch first."},
    {"room":5,"kind":"derive","title":"Final override","prompt":"Enter the final proposition derived by the complete knowledge base.","facts":["P","Q"],"rules":[{"if":["P"],"then":"R"},{"if":["Q"],"then":"S"},{"if":["R","S"],"then":"T"},{"if":["T"],"then":"U"}],"target":"U","hint":"After deriving T, continue chaining: the final rule maps T to one more proposition."},
]
TOTAL = len(PUZZLES)
ROOM_COUNTS = {room["id"]: sum(p["room"] == room["id"] for p in PUZZLES) for room in ROOMS}


# -------------------- Game state and response shaping --------------------
def initial_state():
    return {"started":False,"index":0,"score":0,"lives":START_LIVES,
            "hints_used":0,"hinted":[],"start_time":None,"game_over":False,"escaped":False}


def get_state():
    state = session.get("game")
    if not isinstance(state, dict):
        state = initial_state()
        session["game"] = state
    return state


def elapsed(state):
    return max(0, int(time.time() - state["start_time"])) if state.get("start_time") else 0


def puzzle_result(puzzle):
    if puzzle["kind"] == "evaluate":
        result = eval_expression(puzzle["expression"], puzzle["facts"])
        return result, {"expression":puzzle["expression"],"values":puzzle["facts"],"result":result}
    if puzzle["kind"] in ("infer_boolean", "derive"):
        known, chain = forward_chain(puzzle["facts"], puzzle["rules"])
        result = puzzle["target"] in known
        return result, {"facts":puzzle["facts"],"known":sorted(known),"chain":chain,"target":puzzle["target"],"result":result}
    table = truth_table(puzzle["expression"])
    return table["classification"], {"truth_table":table}


def public_puzzle(puzzle, index, state):
    room = next(r for r in ROOMS if r["id"] == puzzle["room"])
    payload = {key:puzzle[key] for key in ("expression","facts","rules","target","labels") if key in puzzle}
    room_no = sum(1 for p in PUZZLES[:index+1] if p["room"] == puzzle["room"])
    payload.update({"room":puzzle["room"],"room_name":room["name"],"room_tag":room["tag"],
        "accent":room["accent"],"kind":puzzle["kind"],"title":puzzle["title"],"prompt":puzzle["prompt"],
        "number":index+1,"room_puzzle_number":room_no,"room_puzzle_total":ROOM_COUNTS[puzzle["room"]],
        "hint_available":str(index) not in state["hinted"]})
    return payload


def snapshot(state=None):
    state = state or get_state()
    puzzle = PUZZLES[state["index"]] if state["index"] < TOTAL else None
    room_id = puzzle["room"] if puzzle else 5
    room_no = sum(1 for p in PUZZLES[:state["index"]+1] if p["room"] == room_id) if puzzle else 3
    room_progress = []
    for room in ROOMS:
        solved = sum(1 for i,p in enumerate(PUZZLES) if i < state["index"] and p["room"] == room["id"])
        room_progress.append({**room,"solved":solved,"total":ROOM_COUNTS[room["id"]],
            "complete":solved == ROOM_COUNTS[room["id"]],"active":bool(puzzle and puzzle["room"] == room["id"])})
    return {"started":state["started"],"game_over":state["game_over"],"escaped":state["escaped"],
        "score":state["score"],"lives":state["lives"],"hints_used":state["hints_used"],
        "elapsed_seconds":elapsed(state),"index":state["index"],"total_puzzles":TOTAL,
        "progress":min(state["index"],TOTAL),"room":room_id,"room_puzzle_number":room_no,
        "room_puzzle_total":ROOM_COUNTS[room_id],"rooms":room_progress,
        "puzzle":public_puzzle(puzzle,state["index"],state) if puzzle and state["started"] and not state["game_over"] else None}


def body_json():
    value = request.get_json(silent=True)
    return value if isinstance(value,dict) else None


def parse_truth(answer):
    if not isinstance(answer,str): return None
    if answer.strip().upper() in ("TRUE","T","YES","1"): return True
    if answer.strip().upper() in ("FALSE","F","NO","0"): return False
    return None


def check_answer(puzzle, answer, expected):
    kind = puzzle["kind"]
    if kind in ("evaluate","infer_boolean"):
        parsed = parse_truth(answer)
        return None if parsed is None else parsed == bool(expected)
    if not isinstance(answer,str): return None
    if kind == "classify":
        value = answer.strip().upper()
        return value == expected if value in ("TAUTOLOGY","CONTRADICTION","CONTINGENCY") else None
    if kind == "derive":
        value = re.sub(r"[^A-Z0-9_]","",answer.upper())
        return value == puzzle["target"] if value else None
    return None


# -------------------- Flask routes --------------------
@app.get("/")
def home():
    return render_template_string(PAGE)


@app.get("/health")
def health():
    return jsonify({"ok":True,"service":"AI Escape Room"})


@app.get("/api/state")
def api_state():
    return jsonify(snapshot())


@app.post("/api/start")
def api_start():
    state = initial_state()
    state.update(started=True,start_time=time.time())
    session["game"] = state
    return jsonify({"ok":True,"state":snapshot(state)})


@app.post("/api/restart")
def api_restart():
    state = initial_state()
    session["game"] = state
    return jsonify({"ok":True,"state":snapshot(state)})


@app.post("/api/hint")
def api_hint():
    if body_json() is None: return jsonify({"ok":False,"error":"Send a JSON object."}),400
    state = get_state()
    if not state["started"] or state["game_over"] or state["escaped"]:
        return jsonify({"ok":False,"error":"Start an active mission to request a hint."}),409
    puzzle = PUZZLES[state["index"]]
    key = str(state["index"])
    used = key in state["hinted"]
    if not used:
        state["hinted"].append(key)
        state["hints_used"] += 1
        state["score"] += HINT
        session["game"] = state
    return jsonify({"ok":True,"hint":puzzle["hint"],"deducted":0 if used else abs(HINT),
        "already_used":used,"state":snapshot(state)})


@app.post("/api/submit")
def api_submit():
    body = body_json()
    if body is None: return jsonify({"ok":False,"error":"Send a JSON object with an answer."}),400
    state = get_state()
    if not state["started"] or state["game_over"] or state["escaped"]:
        return jsonify({"ok":False,"error":"Start an active mission before submitting."}),409
    puzzle = PUZZLES[state["index"]]
    answer = body.get("answer")
    if not isinstance(answer,str) or not answer.strip():
        return jsonify({"ok":False,"error":"Enter an answer before submitting."}),400
    try:
        expected, reasoning = puzzle_result(puzzle)
    except (LogicError,KeyError,TypeError) as error:
        return jsonify({"ok":False,"error":f"Puzzle configuration error: {error}"}),500
    correct = check_answer(puzzle,answer,expected)
    if correct is None:
        msg = "Choose TRUE or FALSE." if puzzle["kind"] in ("evaluate","infer_boolean") else (
            "Choose TAUTOLOGY, CONTRADICTION, or CONTINGENCY." if puzzle["kind"] == "classify"
            else "Enter a proposition from the inference chain.")
        return jsonify({"ok":False,"error":msg}),400

    room_id = puzzle["room"]
    if correct:
        state["score"] += CORRECT
        state["index"] += 1
        next_puzzle = PUZZLES[state["index"]] if state["index"] < TOTAL else None
        room_completed = next_puzzle is None or next_puzzle["room"] != room_id
        earned = CORRECT
        if room_completed:
            state["score"] += ROOM_BONUS
            earned += ROOM_BONUS
        escaped = state["index"] >= TOTAL
        if escaped:
            state["escaped"] = True
            state["score"] += ESCAPE_BONUS
            earned += ESCAPE_BONUS
        session["game"] = state
        return jsonify({"ok":True,"correct":True,"message":"LOGIC VERIFIED — correct.",
            "earned":earned,"room_completed":room_completed,"escaped":escaped,
            "reasoning":reasoning,"solved_puzzle":{"title":puzzle["title"],"kind":puzzle["kind"]},
            "state":snapshot(state)})
    state["score"] += WRONG
    state["lives"] = max(0,state["lives"]-1)
    if state["lives"] == 0: state["game_over"] = True
    session["game"] = state
    return jsonify({"ok":True,"correct":False,"message":"Not quite. Review the logic and try again.",
        "earned":WRONG,"lives_lost":1,"reasoning":None,"state":snapshot(state)})


@app.post("/api/analyze")
def api_analyze():
    body = body_json()
    if body is None: return jsonify({"ok":False,"error":"Send a JSON object."}),400
    try:
        return jsonify({"ok":True,"analysis":truth_table(body.get("expression"))})
    except LogicError as error:
        return jsonify({"ok":False,"error":str(error)}),400


@app.errorhandler(404)
def not_found(error):
    if request.path.startswith("/api/"): return jsonify({"ok":False,"error":"API route not found."}),404
    return "Not found",404


# -------------------- Single-file frontend --------------------
PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="theme-color" content="#070b12"><title>AI Escape Room — Propositional Logic</title>
<style>
:root{color-scheme:dark;--bg:#070b12;--panel:#101a28;--line:#243246;--muted:#8c9ab0;--text:#edf4ff;--cyan:#68e5df;--blue:#71a8ff;--violet:#c29aff;--green:#89edb7;--red:#ff6e7b;--gold:#f0c979;font-family:Inter,system-ui,-apple-system,"Segoe UI",sans-serif}
*{box-sizing:border-box}body{margin:0;min-height:100vh;color:var(--text);background:radial-gradient(ellipse at 10% 4%,#153039 0,transparent 32rem),radial-gradient(ellipse at 90% 12%,#24203e 0,transparent 30rem),linear-gradient(155deg,#080c14,#070b12)}
body:before{content:"";position:fixed;inset:0;pointer-events:none;opacity:.11;background-image:linear-gradient(#8aa2c014 1px,transparent 1px),linear-gradient(90deg,#8aa2c014 1px,transparent 1px);background-size:52px 52px;mask-image:linear-gradient(#000,transparent 82%)}
button,input{font:inherit}button{color:inherit;cursor:pointer}.shell{width:min(1180px,calc(100% - 36px));margin:auto;position:relative}
header{display:flex;align-items:center;justify-content:space-between;gap:16px;padding:20px 0;border-bottom:1px solid var(--line)}
.brand{display:flex;align-items:center;gap:11px;font-weight:800;font-size:12px;letter-spacing:.1em}.mark{width:38px;height:38px;display:grid;place-items:center;border:1px solid #68e5df66;border-radius:12px;background:#68e5df12;color:var(--cyan);font-size:20px}.brand small{display:block;color:var(--muted);font-size:9px;letter-spacing:.17em;margin-top:4px}
.headright{display:flex;align-items:center;gap:18px}.online{font-size:10px;color:#bfccdc;letter-spacing:.12em}.dot{display:inline-block;width:7px;height:7px;border-radius:50%;background:var(--green);box-shadow:0 0 12px var(--green);margin-right:7px}
nav{display:flex;gap:4px}.nav{border:1px solid transparent;background:none;color:var(--muted);padding:9px 11px;border-radius:8px;font-size:11px}.nav:hover,.nav.active{background:#ffffff09;border-color:var(--line);color:var(--text)}
main{min-height:calc(100vh - 100px);padding:34px 0 56px}.eyebrow{font-size:10px;color:var(--cyan);font-weight:800;letter-spacing:.18em;text-transform:uppercase}.muted,.small{color:var(--muted)}.small{font-size:10px}
.hero{min-height:465px;display:grid;grid-template-columns:1.12fr .88fr;align-items:center;gap:40px;padding:35px 0 45px}.hero h1{font-size:clamp(43px,7vw,78px);line-height:.98;letter-spacing:-.06em;margin:17px 0}.hero h1 span{color:var(--cyan)}.hero p{max-width:550px;color:#adbacb;line-height:1.75;font-size:14px}
.actions{display:flex;gap:9px;flex-wrap:wrap;margin-top:23px}.primary,.secondary,.answer{border-radius:9px;padding:12px 16px;font-size:11px;font-weight:800;transition:.18s}.primary{background:linear-gradient(135deg,#75eee2,#69cce4);border:1px solid transparent;color:#061113;box-shadow:0 7px 24px #68e5df27}.primary:hover{transform:translateY(-2px);box-shadow:0 12px 34px #68e5df40}.secondary,.answer{background:#ffffff08;border:1px solid var(--line);color:#e1ebf7}.secondary:hover,.answer:hover{border-color:#68e5df77;transform:translateY(-1px)}button:focus-visible,input:focus-visible{outline:2px solid var(--cyan);outline-offset:3px}
.visual{position:relative;min-height:330px;display:grid;place-items:center}.orbit{width:min(310px,75vw);aspect-ratio:1;border:1px solid #68e5df55;border-radius:50%;display:grid;place-items:center;position:relative;box-shadow:0 0 65px #28bab71a,inset 0 0 70px #28bab710}.orbit:before,.orbit:after{content:"";position:absolute;border:1px solid #68e5df25;border-radius:50%}.orbit:before{inset:27px}.orbit:after{inset:58px}.core{z-index:1;width:105px;height:105px;display:grid;place-items:center;border:1px solid #68e5df77;border-radius:28px;background:#68e5df1c;color:var(--cyan);font-size:44px;box-shadow:0 0 50px #68e5df2e}.tag{position:absolute;z-index:2;padding:7px 9px;background:#09111b;border:1px solid var(--line);border-radius:6px;font:9px ui-monospace,monospace;color:#bed0e0}.top{top:17px}.right{right:-15px;top:48%}.bottom{bottom:17px}.left{left:-15px;top:48%}.signal{position:absolute;bottom:0;right:0;width:180px;padding:13px;border:1px solid var(--line);border-radius:10px;background:#0d1521}.signal b{display:block;color:var(--muted);font-size:9px;letter-spacing:.13em}.signal span{display:block;color:var(--green);font:11px ui-monospace,monospace;margin-top:8px}
.features{display:grid;grid-template-columns:repeat(3,1fr);border:1px solid var(--line);border-radius:13px;background:#101a2880;overflow:hidden}.feature{padding:18px 20px;border-right:1px solid var(--line)}.feature:last-child{border:0}.feature b{font-size:11px}.feature p{font-size:10px;color:var(--muted);line-height:1.6;margin:7px 0 0}
.sectionhead{display:flex;justify-content:space-between;align-items:end;gap:16px;margin-bottom:20px}.sectionhead h1{margin:7px 0 0;font-size:clamp(27px,4vw,38px);letter-spacing:-.04em}
.panel{border:1px solid var(--line);border-radius:15px;background:linear-gradient(145deg,#111b2bf0,#0b111cf2);box-shadow:0 18px 50px #0002}.grid2,.learn{display:grid;grid-template-columns:repeat(2,1fr);gap:13px}.learn{grid-template-columns:repeat(3,1fr)}.info{padding:19px}.info h3{font-size:13px;margin:0 0 8px}.info p{font-size:11px;line-height:1.65;color:var(--muted);margin:0}.formula{display:inline-block;background:#68e5df0d;border:1px solid #68e5df32;color:var(--cyan);padding:7px 9px;border-radius:7px;font:12px ui-monospace,monospace;margin-top:10px}
.truthdemo{padding:19px;margin-top:13px}.truthcontrols{display:flex;gap:9px;margin:12px 0}input[type=text]{min-width:0;flex:1;background:#090f18;border:1px solid var(--line);border-radius:8px;color:var(--text);padding:11px}
.tablewrap{overflow:auto}table{width:100%;border-collapse:collapse;font:10px ui-monospace,monospace;margin-top:12px}th,td{text-align:center;padding:8px 9px;border-bottom:1px solid var(--line)}th{color:var(--muted);font-weight:600}td:last-child{color:var(--cyan);font-weight:800}.classification{color:var(--gold);font:10px ui-monospace,monospace;margin-top:10px;letter-spacing:.1em}
.hud{display:grid;grid-template-columns:repeat(4,1fr);gap:9px;margin-bottom:15px}.huditem{padding:12px 14px;background:#0e1622;border:1px solid var(--line);border-radius:10px}.huditem span{display:block;color:var(--muted);font-size:9px;text-transform:uppercase;letter-spacing:.13em}.huditem strong{display:block;margin-top:7px;font:16px ui-monospace,monospace}.lives{color:var(--red)}
.gamelayout{display:grid;grid-template-columns:minmax(0,1fr) 265px;gap:14px;align-items:start}.gamemain{overflow:hidden}.banner{padding:20px 22px 17px;border-bottom:1px solid var(--line);position:relative}.banner:before{content:"";position:absolute;left:0;top:0;bottom:0;width:3px;background:var(--cyan)}.gamemain[data-accent=blue] .banner:before{background:var(--blue)}.gamemain[data-accent=violet] .banner:before{background:var(--violet)}.gamemain[data-accent=green] .banner:before{background:var(--green)}.gamemain[data-accent=red] .banner:before{background:var(--red);box-shadow:0 0 20px var(--red)}.bannertop{display:flex;justify-content:space-between;gap:10px;align-items:center}.banner h2{font-size:23px;margin:7px 0 0;letter-spacing:-.04em}.roomcount{font:9px ui-monospace,monospace;color:var(--muted)}.gamebody{padding:22px}.gamebody h3{font-size:18px;margin:8px 0}.prompt{font-size:12px;color:#b5c2d4;line-height:1.65;margin:9px 0 16px}
.logicbox{padding:15px;border:1px solid #68e5df30;border-radius:11px;background:#050b12a8;margin:12px 0}.logiclabel{font-size:9px;color:var(--muted);letter-spacing:.14em;text-transform:uppercase;margin-bottom:8px}.logicline{display:flex;justify-content:space-between;gap:10px;padding:6px 0;color:#c0ccdc;font:10px ui-monospace,monospace}.logicline b{color:var(--cyan);font-weight:600}.expression{font:21px ui-monospace,monospace;color:var(--cyan)}.answers{display:flex;flex-wrap:wrap;gap:8px;margin:15px 0}.answer{min-width:100px}.textanswer{display:flex;gap:8px;margin:15px 0}.feedback{padding:12px 14px;margin-top:14px;border:1px solid var(--line);border-radius:9px;background:#ffffff08;color:#d4dfec;font-size:11px;line-height:1.6}.feedback.good{border-color:#89edb74a;background:#89edb70c}.feedback.bad{border-color:#ff6e7b44;background:#ff6e7b0c}.feedback strong{display:block;color:var(--green);margin-bottom:3px}.feedback.bad strong{color:var(--red)}.reason{font:10px/1.7 ui-monospace,monospace;color:#b5c3d4;margin-top:7px}.gameactions{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-top:16px}.sidebar{padding:16px}.sidebar h3{font-size:10px;letter-spacing:.13em;text-transform:uppercase;color:#c4d1e2;margin:0 0 12px}.roomlist{display:grid;gap:7px}.roomrow{display:flex;align-items:center;gap:9px;padding:8px;border:1px solid transparent;border-radius:8px;color:var(--muted)}.roomrow.active{background:#68e5df0c;border-color:#68e5df30;color:var(--text)}.roomrow.complete .roomnum{color:var(--green)}.roomnum{width:22px;height:22px;border-radius:6px;display:grid;place-items:center;background:#ffffff0a;font:9px ui-monospace,monospace}.roomrow span:nth-child(2){font-size:9px;flex:1}.roomrow small{font:9px ui-monospace,monospace}.separator{height:1px;background:var(--line);margin:14px 0}.track{height:5px;background:#ffffff12;border-radius:99px;overflow:hidden;margin-top:8px}.fill{height:100%;background:linear-gradient(90deg,var(--cyan),var(--green))}
.error{color:var(--red);font-size:10px;min-height:16px}.result{text-align:center;padding:45px 24px}.resulticon{font-size:38px;color:var(--cyan)}.result h1{font-size:clamp(34px,6vw,56px);letter-spacing:-.05em;margin:10px}.result p{color:var(--muted);font-size:12px}.stats{display:flex;flex-wrap:wrap;justify-content:center;gap:9px;margin:22px 0}.stat{min-width:125px;padding:13px;border:1px solid var(--line);border-radius:9px;background:#ffffff06}.stat span{display:block;color:var(--muted);font-size:8px;text-transform:uppercase;letter-spacing:.12em}.stat b{display:block;margin-top:7px;font:16px ui-monospace,monospace}.concepts{display:flex;flex-wrap:wrap;justify-content:center;gap:7px;margin:17px auto;max-width:680px}.concepts span{padding:6px 9px;border:1px solid #68e5df30;border-radius:30px;color:#b9d9d8;font-size:9px}
.toast{position:fixed;right:20px;bottom:18px;max-width:min(390px,calc(100vw - 38px));z-index:5;padding:12px 15px;border:1px solid var(--line);border-radius:10px;background:#101a28;box-shadow:0 12px 38px #0006;font-size:11px}.hidden{display:none!important}footer{border-top:1px solid var(--line);padding:17px 0 22px;text-align:center;color:#58677c;font-size:9px;letter-spacing:.05em}
@media(max-width:850px){.gamelayout{grid-template-columns:1fr}.sidebar{order:-1}.roomlist{grid-template-columns:repeat(5,1fr)}.roomrow{display:grid;justify-items:center;text-align:center;padding:6px 2px;gap:4px}.roomrow span:nth-child(2){font-size:7px}.roomrow small{display:none}}
@media(max-width:650px){.shell{width:calc(100% - 24px)}header{padding:14px 0}.headright{gap:5px}.online{display:none}.nav{padding:8px 6px;font-size:9px}.hero{grid-template-columns:1fr;gap:8px;padding:26px 0 35px}.hero h1{font-size:clamp(43px,13vw,68px)}.visual{min-height:285px}.orbit{width:260px}.signal{right:1%;bottom:0}.features{grid-template-columns:1fr}.feature{border-right:0;border-bottom:1px solid var(--line);padding:14px 16px}.feature:last-child{border:0}.grid2,.learn{grid-template-columns:1fr}.hud{grid-template-columns:repeat(2,1fr)}.gamebody,.banner{padding-left:16px;padding-right:16px}.textanswer,.truthcontrols{flex-direction:column}.textanswer .primary,.truthcontrols .primary{width:100%}.gameactions{align-items:flex-start;flex-direction:column}}
@media(prefers-reduced-motion:reduce){*,*:before,*:after{scroll-behavior:auto!important;transition:none!important}}
</style></head>
<body><div class="shell"><header><div class="brand"><div class="mark" aria-hidden="true">⌘</div><div>AI ESCAPE ROOM<small>SYMBOLIC REASONING LAB</small></div></div><div class="headright"><div class="online"><i class="dot"></i>SYSTEM ONLINE</div><nav aria-label="Main navigation"><button class="nav active" data-view="home">Home</button><button class="nav" data-view="instructions">How to play</button><button class="nav" data-view="learn">Learn logic</button></nav></div></header><main id="app"></main><footer>SYMBOLIC AI // FACTS + RULES → INFERENCE // NO GENERATIVE AI REQUIRED</footer></div><div id="toast" class="toast hidden" role="status" aria-live="polite"></div>
<script>
const root=document.getElementById('app');let game=null,elapsed=0,view='home',feedback=null,timerToast;
async function api(path,method='GET',body){const r=await fetch(path,{method,headers:body?{'Content-Type':'application/json'}:{},body:body?JSON.stringify(body):undefined});let d;try{d=await r.json()}catch(e){throw Error('Server response could not be read.')}if(!r.ok||d.ok===false)throw Error(d.error||'Request failed.');return d}
function esc(s){return String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
function duration(n){return `${String(Math.floor(n/60)).padStart(2,'0')}:${String(n%60).padStart(2,'0')}`}
function toast(s){let t=document.getElementById('toast');t.textContent=s;t.classList.remove('hidden');clearTimeout(timerToast);timerToast=setTimeout(()=>t.classList.add('hidden'),3300)}
function nav(v){view=v;document.querySelectorAll('.nav').forEach(b=>b.classList.toggle('active',b.dataset.view===v));render();window.scrollTo({top:0,behavior:'smooth'})}
document.querySelectorAll('.nav').forEach(b=>b.onclick=()=>nav(b.dataset.view));
async function refresh(){try{game=await api('/api/state');elapsed=game.elapsed_seconds||0;if(game.escaped||game.game_over)view='result';else if(game.started)view='game';render()}catch(e){toast(e.message)}}
async function start(){try{game=(await api('/api/start','POST',{})).state;elapsed=game.elapsed_seconds||0;feedback=null;nav('game')}catch(e){toast(e.message)}}
async function restart(){try{game=(await api('/api/restart','POST',{})).state;feedback=null;view='home';nav('home')}catch(e){toast(e.message)}}
function home(){return `<section class="hero"><div><div class="eyebrow">CLASSICAL AI // INTERACTIVE SIMULATION</div><h1>Think in<br><span>propositions.</span></h1><p>A research facility has sealed its doors. Use symbolic logic, rule-based reasoning, and forward chaining to restore access—one system at a time.</p><div class="actions"><button class="primary" onclick="start()">START MISSION ↗</button><button class="secondary" onclick="nav('instructions')">HOW TO PLAY</button><button class="secondary" onclick="nav('learn')">LEARN LOGIC</button></div></div><div class="visual"><div class="orbit"><span class="tag top">KB / ACTIVE</span><span class="tag right">RULES</span><span class="tag bottom">INFERENCE</span><span class="tag left">FACTS</span><div class="core">⌬</div></div><div class="signal"><b>REASONING ENGINE</b><span>READY · 5 SECTORS</span></div></div></section><section class="features"><div class="feature"><b>01 / SYMBOLIC LOGIC</b><p>Evaluate AND, OR, NOT, and implication using a safe logic parser.</p></div><div class="feature"><b>02 / RULE-BASED AI</b><p>Apply Modus Ponens and chain facts into new conclusions.</p></div><div class="feature"><b>03 / TRUTH ANALYSIS</b><p>Generate truth tables for tautologies, contradictions, and contingencies.</p></div></section>`}
function instructions(){return `<div class="sectionhead"><div><div class="eyebrow">FIELD GUIDE / 00</div><h1>How to play</h1></div><button class="primary" onclick="start()">BEGIN MISSION ↗</button></div><div class="grid2">
<article class="panel info"><h3>Mission objective</h3><p>Clear five facility sections with three logic challenges each. The backend evaluates each formula and inference chain before accepting an answer.</p></article>
<article class="panel info"><h3>Lives & score</h3><p>Start with three lives. Correct answers earn 100 points, wrong answers cost 20 points and one life, clearing a room adds 150, and escaping adds 500.</p></article>
<article class="panel info"><h3>Hints & timer</h3><p>Each puzzle has a concept-focused hint. The first hint on a puzzle costs 25 points; it can be reopened without another deduction. The timer starts with your mission.</p></article>
<article class="panel info"><h3>Operators</h3><p>AND needs both sides true. OR needs at least one. NOT reverses truth. IMPLIES is false only when its premise is true and its conclusion is false.</p><span class="formula">P ∧ Q · P ∨ Q · ¬P · P → Q</span></article>
<article class="panel info"><h3>Inference</h3><p>A knowledge base stores facts and rules. Forward chaining repeatedly fires rules whose premises are known. From P → Q and fact P, Modus Ponens derives Q.</p><span class="formula">P → Q &nbsp;+&nbsp; P ⟹ Q</span></article>
<article class="panel info"><h3>Winning</h3><p>Complete all 15 puzzles to open the AI Core and see your score, lives, hints, and final time.</p></article></div>`}
function learn(){return `<div class="sectionhead"><div><div class="eyebrow">LOGIC PRIMER / 01</div><h1>Learn the language</h1></div><span class="small">Try formulas below—no code execution is involved.</span></div><div class="learn">
<article class="panel info"><h3>Propositions</h3><p>A statement that is either true or false.</p><span class="formula">P = Door is locked</span></article><article class="panel info"><h3>AND · ∧</h3><p>True only when both are true.</p><span class="formula">P ∧ Q</span></article><article class="panel info"><h3>OR · ∨</h3><p>True when at least one is true.</p><span class="formula">P ∨ Q</span></article><article class="panel info"><h3>NOT · ¬</h3><p>Reverses the truth value.</p><span class="formula">¬P</span></article><article class="panel info"><h3>IMPLIES · →</h3><p>False only when P is true and Q is false.</p><span class="formula">P → Q</span></article><article class="panel info"><h3>Knowledge & chaining</h3><p>Facts plus rules make a knowledge base. Forward chaining derives facts until no rule can fire.</p><span class="formula">P → Q, P ⟹ Q</span></article></div>
<section class="panel truthdemo"><div class="eyebrow">INTERACTIVE / TRUTH TABLE</div><h3 style="margin:8px 0">Analyze a formula</h3><p class="small">Use P, Q, R; parentheses; and ∧, ∨, ¬, → (or AND, OR, NOT, IMPLIES).</p><div class="truthcontrols"><input id="expr" value="(P → Q) ∧ P" aria-label="Logical expression"><button class="primary" onclick="analyze()">GENERATE TABLE</button></div><div id="analysis"></div></section>`}
function tableHtml(t){let head=[...t.variables,t.expression].map(x=>`<th>${esc(x)}</th>`).join('');let rows=t.rows.map(row=>`<tr>${t.variables.map(v=>`<td>${row.values[v]?'TRUE':'FALSE'}</td>`).join('')}<td>${row.result?'TRUE':'FALSE'}</td></tr>`).join('');return `<div class="tablewrap"><table><thead><tr>${head}</tr></thead><tbody>${rows}</tbody></table></div><div class="classification">${esc(t.classification)} · ${t.satisfiable?'SATISFIABLE':'UNSATISFIABLE'}</div>`}
async function analyze(){let out=document.getElementById('analysis');try{out.innerHTML=tableHtml((await api('/api/analyze','POST',{expression:document.getElementById('expr').value})).analysis)}catch(e){out.innerHTML=`<div class="error">${esc(e.message)}</div>`}}
function hud(){let hearts=Array.from({length:3},(_,i)=>i<game.lives?'♥':'♡').join(' ');return `<div class="hud"><div class="huditem"><span>Score</span><strong>${game.score}</strong></div><div class="huditem"><span>Lives remaining</span><strong class="lives">${hearts}</strong></div><div class="huditem"><span>Hints used</span><strong>${game.hints_used}</strong></div><div class="huditem"><span>Mission time</span><strong id="timer">${duration(elapsed)}</strong></div></div>`}
function sidebar(){let list=game.rooms.map(r=>`<div class="roomrow ${r.active?'active':''} ${r.complete?'complete':''}"><span class="roomnum">${r.complete?'✓':String(r.id).padStart(2,'0')}</span><span>${esc(r.name)}</span><small>${r.solved}/${r.total}</small></div>`).join('');let pct=Math.round(100*game.progress/game.total_puzzles);return `<aside class="panel sidebar"><h3>Facility map</h3><div class="roomlist">${list}</div><div class="separator"></div><div class="small">Mission progress <span style="float:right">${pct}%</span></div><div class="track"><div class="fill" style="width:${pct}%"></div></div><div class="small" style="margin-top:8px">${game.progress} of ${game.total_puzzles} puzzles solved</div></aside>`}
function logicBox(p){if(p.kind==='evaluate'){let lines=Object.entries(p.facts).map(([k,v])=>`<div class="logicline"><span>${esc(k)} · ${esc(p.labels[k]||k)}</span><b>${v?'TRUE':'FALSE'}</b></div>`).join('');return `<div class="logicbox"><div class="logiclabel">Current propositions</div>${lines}<div class="separator"></div><div class="expression">${esc(p.expression)}</div></div>`}if(p.kind==='classify')return `<div class="logicbox"><div class="logiclabel">Formula under analysis</div><div class="expression">${esc(p.expression)}</div></div>`;let facts=p.facts.map(x=>`<span class="formula">${esc(x)}</span>`).join(' ');let rules=p.rules.map(r=>`<div class="logicline"><span>${r.if.map(esc).join(' ∧ ')}</span><b>→ ${esc(r.then)}</b></div>`).join('');return `<div class="logicbox"><div class="logiclabel">Known facts</div>${facts}<div class="separator"></div><div class="logiclabel">Rule set</div>${rules}${p.kind==='infer_boolean'?`<div class="small" style="margin-top:9px">Target: <b style="color:var(--cyan)">${esc(p.target)}</b></div>`:''}</div>`}
function answerUi(p){if(['evaluate','infer_boolean'].includes(p.kind))return `<div class="answers"><button class="answer" onclick="submit('TRUE')">TRUE</button><button class="answer" onclick="submit('FALSE')">FALSE</button></div>`;if(p.kind==='classify')return `<div class="answers">${['TAUTOLOGY','CONTRADICTION','CONTINGENCY'].map(v=>`<button class="answer" onclick="submit('${v}')">${v}</button>`).join('')}</div>`;return `<form class="textanswer" onsubmit="event.preventDefault();submit(document.getElementById('proposition').value)"><input id="proposition" maxlength="24" placeholder="Enter proposition, e.g. U" aria-label="Final proposition"><button class="primary">SUBMIT ↗</button></form>`}
function reasoning(f){if(!f?.reasoning)return '';let r=f.reasoning;if(r.truth_table)return tableHtml(r.truth_table);if(r.expression){let values=Object.entries(r.values).map(([k,v])=>`${k}=${v?'TRUE':'FALSE'}`).join(' · ');return `<div class="reason">${esc(values)}<br>${esc(r.expression)} = ${r.result?'TRUE':'FALSE'}</div>`}let steps=r.chain.map(s=>`${s.premises.map(esc).join(' ∧ ')} → ${esc(s.conclusion)}`).join('<br>');return `<div class="reason">DERIVED FACTS: ${r.known.map(esc).join(', ')}<br>${steps||'No rule fired; target is not derivable.'}</div>`}
function feedbackHtml(f){if(!f)return '';let good=f.correct;let title=good?(f.escaped?'✓ AI CORE UNLOCKED':'✓ CORRECT — LOGIC VERIFIED'):'× INCORRECT';let detail=good?`+${f.earned} points${f.room_completed&&!f.escaped?' · Section cleared':''}${f.escaped?' · Escape bonus included':''}`:`${f.earned} points · ${f.state.lives} ${f.state.lives===1?'life':'lives'} remaining`;return `<div class="feedback ${good?'good':'bad'}" role="status"><strong>${title}</strong>${detail}${reasoning(f)}</div>`}
function gameView(){if(!game?.puzzle)return resultView();let p=game.puzzle;return `${hud()}<div class="gamelayout"><section class="panel gamemain" data-accent="${esc(p.accent)}"><div class="banner"><div class="bannertop"><span class="eyebrow">${esc(p.room_tag)} / ROOM ${p.room}</span><span class="roomcount">CHALLENGE ${p.room_puzzle_number} / ${p.room_puzzle_total}</span></div><h2>${esc(p.room_name)}</h2></div><div class="gamebody"><div class="eyebrow">PUZZLE ${String(p.number).padStart(2,'0')} / ${game.total_puzzles}</div><h3>${esc(p.title)}</h3><p class="prompt">${esc(p.prompt)}</p>${logicBox(p)}<div class="logiclabel">Select your conclusion</div>${answerUi(p)}<div id="submit-error" class="error" role="alert"></div>${feedbackHtml(feedback)}<div class="gameactions"><button class="secondary" onclick="hint()">REVEAL HINT −25</button><span class="small">The server checks the actual logic.</span></div></div></section>${sidebar()}</div>`}
function resultView(){if(!game?.started)return home();let won=game.escaped;return `${hud()}<section class="panel result"><div class="resulticon">⌑</div><div class="eyebrow">${won?'SECURITY OVERRIDE COMPLETE':'MISSION TERMINATED'}</div><h1>${won?'You escaped.':'System locked.'}</h1><p>${won?'The AI Core accepted the proof. The facility is secure.':'All lives were used. Restart the mission to try again.'}</p><div class="stats"><div class="stat"><span>Puzzles solved</span><b>${game.progress} / ${game.total_puzzles}</b></div><div class="stat"><span>Final score</span><b>${game.score}</b></div><div class="stat"><span>Lives remaining</span><b>${game.lives} / 3</b></div><div class="stat"><span>Hints used</span><b>${game.hints_used}</b></div><div class="stat"><span>Mission time</span><b>${duration(game.elapsed_seconds||elapsed)}</b></div></div>${won?'<div class="eyebrow">CONCEPTS VERIFIED</div><div class="concepts"><span>Propositions</span><span>AND / OR / NOT</span><span>Implication</span><span>Modus Ponens</span><span>Knowledge Bases</span><span>Forward Chaining</span><span>Truth Tables</span><span>Satisfiability</span><span>Contradictions</span></div>':''}<div class="actions" style="justify-content:center"><button class="primary" onclick="start()">PLAY AGAIN ↗</button><button class="secondary" onclick="restart()">MAIN MENU</button></div></section>`}
function render(){document.querySelectorAll('.nav').forEach(b=>b.classList.toggle('active',b.dataset.view===view));root.innerHTML=view==='game'&&game?.started?gameView():view==='result'?resultView():view==='instructions'?instructions():view==='learn'?learn():home()}
async function submit(answer){let err=document.getElementById('submit-error');if(err)err.textContent='';try{let d=await api('/api/submit','POST',{answer:String(answer)});game=d.state;elapsed=game.elapsed_seconds||elapsed;feedback=d;view=game.escaped||game.game_over?'result':'game';render()}catch(e){if(err)err.textContent=e.message;else toast(e.message)}}
async function hint(){try{let d=await api('/api/hint','POST',{});game=d.state;feedback=null;render();toast(`${d.hint}${d.deducted?` (${d.deducted} point deduction)`:' (already unlocked)'}`)}catch(e){toast(e.message)}}
setInterval(()=>{if(game?.started&&!game.escaped&&!game.game_over){elapsed++;let t=document.getElementById('timer');if(t)t.textContent=duration(elapsed)}},1000);refresh();
</script></body></html>"""


if __name__ == "__main__":
    print("=" * 52)
    print("       AI ESCAPE ROOM SERVER")
    print("=" * 52)
    print("\nServer running at:\n\nhttp://127.0.0.1:5000\n\nPress CTRL+C to stop.")
    app.run(host="127.0.0.1", port=5000, debug=False)
