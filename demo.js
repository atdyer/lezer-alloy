import { basicSetup, EditorState, EditorView } from "@codemirror/next/basic-setup";

import {parser} from "./dist/index.es"
import {LezerSyntax, foldNodeProp, indentNodeProp} from "@codemirror/next/syntax"
import {styleTags} from "@codemirror/next/highlight"
import {keymap, ViewPlugin, Decoration} from "@codemirror/next/view";
import {RangeSetBuilder} from "@codemirror/next/rangeset";

const output = document.getElementById('output');
const simple = String.raw`pred Deadlock {
    some Process
    some s: State | all p: Process | some Test
}`
const model = String.raw`open util/graph[Course]

one sig Program {
  courses: set Course
}

sig Course {
  reqs: set Course
}

pred prerequisites {
  -- a course cannot be its own prereq
  all c: Course | c not in c.^reqs
  --  a coure can have at most one prereq
  all c: Course | lone c.reqs
}

fun graduationPlan: Program {{
  p: Program {
    -- exactly two courses to graduate
    #p.courses = 2
    -- must take prereqs
    all c: p.courses | some c.reqs => c.reqs in p.courses
  }
}}

pred showSuccessfulPlan {
  prerequisites and some graduationPlan
}

run showSuccessfulPlan for 4`;
const big = String.raw`module examples/algorithms/dijkstra

/*
 * Models how mutexes are grabbed and released by processes, and
 * how Dijkstra's mutex ordering criterion can prevent deadlocks.
 *
 * For a detailed description, see:
 *   E. W. Dijkstra, Cooperating sequential processes. Technological
 *   University, Eindhoven, The Netherlands, September 1965.
 *   Reprinted in Programming Languages, F. Genuys, Ed., Academic
 *   Press, New York, 1968, 43-112.
 *
 * Acknowledgements to Ulrich Geilmann for finding and fixing a bug
 * in the GrabMutex predicate.
 *   
 */

open util/ordering [State] as so
open util/ordering [Mutex] as mo

sig Process {}
sig Mutex {}

sig State { holds, waits: Process -> Mutex }


pred Initial [s: State]  { no s.holds + s.waits }

pred IsFree [s: State, m: Mutex] {
   // no process holds this mutex
   no m.~(s.holds)
   // all p: Process | m !in p.(this.holds)
}

pred IsStalled [s: State, p: Process] { some p.(s.waits) }

pred GrabMutex [s: State, p: Process, m: Mutex, s': State] {
   // a process can only act if it is not
   // waiting for a mutex
   !s.IsStalled[p]
   // can only grab a mutex we do not yet hold
   m !in p.(s.holds)
   // mutexes are grabbed in order
   all m': p.(s.holds) | mo/lt[m',m]
   s.IsFree[m] => {
      // if the mutex is free, we now hold it,
      // and do not become stalled
      p.(s'.holds) = p.(s.holds) + m
      no p.(s'.waits)
   } else {
    // if the mutex was not free,
    // we still hold the same mutexes we held,
    // and are now waiting on the mutex
    // that we tried to grab.
    p.(s'.holds) = p.(s.holds)
    p.(s'.waits) = m
  }
  all otherProc: Process - p | {
     otherProc.(s'.holds) = otherProc.(s.holds)
     otherProc.(s'.waits) = otherProc.(s.waits)
  }
}

pred ReleaseMutex [s: State, p: Process, m: Mutex, s': State] {
   !s.IsStalled[p]
   m in p.(s.holds)
   p.(s'.holds) = p.(s.holds) - m
   no p.(s'.waits)
   no m.~(s.waits) => {
      no m.~(s'.holds)
      no m.~(s'.waits)
   } else {
      some lucky: m.~(s.waits) | {
        m.~(s'.waits) = m.~(s.waits) - lucky
        m.~(s'.holds) = lucky
      }
   }
  all mu: Mutex - m {
    mu.~(s'.waits) = mu.~(s.waits)
    mu.~(s'.holds)= mu.~(s.holds)
  }
}

// for every adjacent (pre,post) pair of States,
// one action happens: either some process grabs a mutex,
// or some process releases a mutex,
// or nothing happens (have to allow this to show deadlocks)
pred GrabOrRelease  {
    Initial[so/first] &&
    (
    all pre: State - so/last  | let post = so/next [pre] |
       (post.holds = pre.holds && post.waits = pre.waits)
        ||
       (some p: Process, m: Mutex | pre.GrabMutex [p, m, post])
        ||
       (some p: Process, m: Mutex | pre.ReleaseMutex [p, m, post])

    )
}

pred Deadlock  {
         some Process
         some s: State | all p: Process | some p.(s.waits)
}

assert DijkstraPreventsDeadlocks {
   GrabOrRelease => ! Deadlock
}


pred ShowDijkstra  {
    GrabOrRelease && Deadlock
    some waits
}

run Deadlock for 3 expect 1
run ShowDijkstra for 5 State, 2 Process, 2 Mutex expect 1
check DijkstraPreventsDeadlocks for 5 State, 5 Process, 4 Mutex expect 0
`;

let hstart = 0;
let hend = 0;

let alloySyntax = LezerSyntax.define(parser.withProps(
    foldNodeProp.add({
        "Block SignatureBlock"(tree) { return { from: tree.start + 1, to: tree.end - 1} },
        BlockComment(tree) { return { from: tree.start + 2, to: tree.end - 2} },
    }),
    indentNodeProp.add(type => {
        if (type.name === "BlockComment") return () => -1;
        return undefined;
    }),
    styleTags({
        LineComment: 'lineComment',
        BlockComment: 'blockComment',
        Number: 'integer',
        CompareOperator: 'compareOperator',
        Name: 'name',
        "abstract fact fun Int module open pred private sig": 'keyword definition',
        "( )": 'paren',
        "[ ]": 'squareBracket',
        "{ }": 'brace'
        // ModuleDeclaration: 'namespace',
        // Name: 'atom',
        // QualName: 'atom',
        // Multiplicity: 'atom',
        // LineComment: 'lineComment',
        // BlockComment: 'blockComment',
        // "module open sig": "keyword definition",
        // "abstract": "modifier",
        // "( )": "paren",
        // "[ ]": "squareBracket",
        // "{ }": "brace"
        // QualName: 'null'
        // Signature: 'string',
        // String: 'string',
        // 'True False': 'atom',
        // Null: 'null',
        // PropertyName: 'propertyName'
    })
))

function printTree () {
    return keymap([{
        key: "Shift-Enter",
        run(target) {
            showTree(target);
            return true;
        }
    }])
}

function showTree (target) {
    try {
        const text = target.state.doc.sliceString(0);
        const tree = parser.parse(text, {strict: false});
        let indent = 0;
        output.innerHTML = '';
        tree.iterate({
            enter: (type, start, end) => {
                const text = '    '.repeat(indent) + type.name + ` [${start}, ${end}]`;
                const pre = document.createElement("pre");
                pre.innerHTML = text;
                pre.onmouseenter = () => {
                    pre.className = 'highlight';
                    setHighlight(start, end);
                }
                pre.onmouseleave = () => {
                    pre.className = '';
                }
                pre.style.cursor = 'pointer';
                output.appendChild(pre);
                indent += 1;
            },
            leave: () => {
                indent -= 1;
            }
        });
    } catch (e) {
        console.log(e);
    }
}

const marker = Decoration.mark({
    class: 'highlight'
});

const setHighlight = (start, end) => {
    hstart = start;
    hend = end;
    view.dispatch({});
}

function parseView () {
    let builder = new RangeSetBuilder();
    builder.add(hstart, hend, marker);
    return builder.finish();
}

const showTokens = ViewPlugin.fromClass(class {
    constructor (view) {
        this.decorations = parseView(view);
    }
    update (update) {
        this.decorations = parseView(update.view);
    }
}, {
    decorations: v => v.decorations
});

let view = new EditorView({state: EditorState.create({
        doc: big,
        extensions: [
            basicSetup,
            alloySyntax,
            printTree(),
            showTokens
        ]
    })});

document.getElementById('editor').appendChild(view.dom);
showTree(view);

