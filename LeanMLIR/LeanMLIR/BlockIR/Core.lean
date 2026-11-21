/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std

/-!
# Block IR: the minimal trusted core

This file is the *entire* trusted semantic base for programs lowered to Block IR.
It depends only on `Std`.

A program is a list of untyped blocks. Each block binds its arguments by name and
runs a list of instructions. An instruction is a primitive operation (from an
`OpAlgebra`), a `call` of a block, or a `ret`.

Call and return targets are *data* (label reflection): `toBlockIdx?` reads a value
as a block index. So all data-dependent control flow (`if`, `switch`, loops,
indirect branches) is just a primop that computes a label, followed by a `call`
on the register holding it.

Everything else — structured control flow such as `scf.for` / `scf.if`, and the
intrinsically typed `Expr` / `Com` front end — is defined *on top of* this file by
translation (ShallowSSA → BlockSSA → BlockIR), so it does not add to the trust base.
-/

/-- An operator algebra: primitive ops with untyped operational semantics. -/
structure OpAlgebra where
  PrimOp : Type
  Data : Type
  State : Type
  eval (op : PrimOp) : State → List Data → Option (List Data × State)
  /-- used for blocks with no return value -/
  novalue : Data
  /-- label/blockidx reflection: a jump whose destination label depends on the value
    of a register, e.g. `if` and `switch` statements. -/
  toBlockIdx? : Data → Option Nat
  /-- the label of a block, as data (inverse to `toBlockIdx?`). Not used by `Block.eval`;
    lowerings use it to emit static jump targets. -/
  ofBlockIdx : Nat → Data

namespace OpAlgebra

variable (opAlg : OpAlgebra)

inductive Arg where
  | ofData (data : opAlg.Data)
  | ofVar (var : String)

inductive Op where
  /-- call the block labelled by the value of `target` -/
  | call (target : opAlg.Arg)
  /-- return to the call site of the block labelled by `target`.
    If multiple calls to that block are on the call stack, returns to the
    latest call added to the call stack. -/
  | ret (target : opAlg.Arg)
  /-- a primitive operation of the algebra -/
  | ofPrimOp (primOp : opAlg.PrimOp)

/--
  apply `op` to `args` and store the returned values in `registers`.
  Ops may have multiple return values (e.g. Go's multiple returns),
  although most IRs will only have one return value per function.
-/
structure Instruction where
  registers : List String
  op : opAlg.Op
  args : List opAlg.Arg

structure Block (opAlg : OpAlgebra) where
  args : List String
  instructions : List opAlg.Instruction

end OpAlgebra

/-- `List.zip` but returns none if the lists are not the same length -/
def List.zip? {α : Type u} {β : Type v} : List α → List β → Option (List (Prod α β)) :=
  fun as bs =>
    if as.length == bs.length then
      some (as.zip bs)
    else
      none

def List.findLastIdx? (p : α → Bool) (l : List α) : Option Nat :=
  (l.reverse.findIdx? p).map (l.length - 1 - ·)

def List.dropFromLast [BEq α] (x : α) (l : List α) : List α :=
  match l.findLastIdx? (· == x) with
  | some i => l.take i
  | none   => l

namespace OpAlgebra

variable {opAlg : OpAlgebra}

def Arg.instantiate (arg : opAlg.Arg) (env : Std.HashMap String opAlg.Data) : Option opAlg.Data :=
  match arg with
  | .ofData data => some data
  | .ofVar var => env.get? var

structure BlockResult (opAlg : OpAlgebra) where
  callStack : List Nat
  retVals : List opAlg.Data
  state : opAlg.State

/--
Run `block` with `args`. Callees see the caller's environment (dynamic scoping),
extended with their own block arguments.

A callee hands back the call stack it returned to. If that stack is *shorter* than
ours, a `ret` unwound past us, so we propagate it; otherwise control resumes here.
-/
def Block.eval (blocks : List (Block opAlg))
    (state : opAlg.State) (env : Std.HashMap String opAlg.Data)
    /- list of block idxs in the current call stack -/
    (callStack : List Nat)
    (block : Block opAlg) (args : List opAlg.Data) :
    Option opAlg.BlockResult := do
  let mut env := env
  for (argName, argVal) in ← block.args.zip? args do
    env := env.insert argName argVal
  let mut state := state
  for instr in block.instructions do
    let inputs ← instr.args.mapM (·.instantiate env)
    let (retVals, state') ← match instr.op with
    | .call target =>
      let i ← opAlg.toBlockIdx? (← target.instantiate env)
      let b ← blocks[i]?
      let ⟨callStack', retVals, state'⟩ ← b.eval blocks state env (callStack ++ [i]) inputs
      if callStack'.length < callStack.length then
        return ⟨callStack', retVals, state'⟩
      pure (retVals, state')
    | .ret target =>
      let i ← opAlg.toBlockIdx? (← target.instantiate env)
      return ⟨callStack.dropFromLast i, inputs, state⟩
    | .ofPrimOp p =>
      opAlg.eval p state inputs
    for (register, retVal) in ← instr.registers.zip? retVals do
      env := env.insert register retVal
    state := state'
  return ⟨callStack.dropLast, [opAlg.novalue], state⟩
partial_fixpoint

/-- A program: a list of blocks plus an entry block. -/
structure Program (opAlg : OpAlgebra) where
  blocks : List (Block opAlg)
  entry : Nat

/-- Run a program from its entry block. -/
def Program.run (p : Program opAlg) (state : opAlg.State) (args : List opAlg.Data) :
    Option (List opAlg.Data × opAlg.State) := do
  let b ← p.blocks[p.entry]?
  let r ← b.eval p.blocks state {} [p.entry] args
  return (r.retVals, r.state)

end OpAlgebra
