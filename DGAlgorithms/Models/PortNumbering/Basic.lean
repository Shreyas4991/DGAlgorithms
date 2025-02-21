import DGAlgorithms.Models.Fingraph
import DGAlgorithms.Models.GraphBasics
import Mathlib

set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace DG

variable (V : Type)
variable [iFin : FinEnum V] [iDec : DecidableEq V] [iRepr: Repr V]


structure PNNode (α : Type) where
  State : Type
  Msg : Type
  Ports : Type
  initState : State
  currentState : State
  inbox : Ports → Option Msg
  outbox : Ports → Option Msg
  Alg : (inp : State)
    → (inbox : Ports → Option Msg)
      → State × (Ports → Option Msg)

open PNNode



def updateNode (p : PNNode V) : PNNode v :=
  {
    State := p.State
    Msg := p.Msg
    Ports := p.Ports
    initState := p.initState
    Alg := p.Alg
    currentState := (p.Alg p.currentState p.inbox).fst
    inbox := p.inbox -- separate updates of the node from the reception of messages
    outbox := (p.Alg p.currentState p.inbox).snd
  }


-- This is a helper function. The actual message received can only be
-- determined when the messages sent by the neighbours are known.
def recvMsg (v : PNNode V) [DecidableEq v.Ports]
    (port : v.Ports) (msg : Option v.Msg): PNNode V := {
      State := v.State
      Msg := v.Msg
      Ports := v.Ports
      initState := v.initState
      Alg := v.Alg
      currentState := v.currentState
      inbox := fun p => if p = port then msg else (v.inbox p)
      outbox := v.outbox
    }

def sendMsg (v : PNNode V) [DecidableEq v.Ports] (port : v.Ports) (msg : Option v.Msg): PNNode V:= {
      State := v.State
      Msg := v.Msg
      Ports := v.Ports
      initState := v.initState
      Alg := v.Alg
      currentState := v.currentState
      inbox := v.inbox
      outbox := fun p => if p = port then msg else v.outbox p
    }

@[reducible]
def initNode (StateType MsgType: Type) (deg : ℕ) (initState : StateType) : PNNode V where
  State := StateType
  Msg := MsgType
  Ports := Fin deg
  initState := initState
  currentState := initState
  inbox := fun _ => none
  outbox := fun _ => none
  Alg := fun _ _ => (initState, fun _ => none) -- default alg does nothing

omit iFin iDec iRepr in
lemma portsType_Findeg : ∀ v : V, ∀ StateType MsgType : Type,
  ∀ initState : StateType,
  (initNode V StateType MsgType deg initState).Ports = Fin deg := by
  intro v ST MT initS
  rfl

def addAlg (n : PNNode V)
  (alg : n.State → (n.Ports → Option n.Msg) → (n.State × (n.Ports → Option n.Msg)))
  : PNNode V :=
  {n with Alg := alg}

structure PNNetwork where
  G : SimpleFinGraph V
  nodes : V → PNNode V
  port_map :
    (v w : V) → (p : (nodes v).Ports) → ((nodes w).Ports)
  port_map_consistent : ∀ (v w : V) (p : (nodes v).Ports),
    port_map w v (port_map v w p) = p ∧ w ∈ G.adj v

def initNetwork [Inhabited V]
  (StateType MsgType: Type)
  (initMap : V → StateType)
  (G : SimpleFinGraph V): PNNetwork V where
  G := G
  nodes := fun v => initNode V StateType MsgType (deg_v V G v) (initMap v)
  port_map := fun v w =>
    let nbrs_w := List.filter (fun z => z ∈ G.adj w) (FinEnum.toList V)
    fun p => by
      rw[portsType_Findeg] at *
      let inw := (List.indexOf p w)
      exact  w
      sorry
  port_map_consistent := sorry

structure PNRun where
  net : PNNetwork V
  round : ℕ


-- This is a test def
def nullRound (pnnet : PNRun V) : PNRun V := {
  round := pnnet.round + 1
  net := pnnet.net
}

inductive PN_OpSem where
  | initialise (run : PNRun V)
  | step (run : PNRunV) -- state, node, next state and next node.


end DG
