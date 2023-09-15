# Ltac2-triggers

## Why do we need a trigger language?

Our goal is to implement an "orchestrator tactic", 
which takes as input several tactics and applies 
them automatically.

As this orchestrator should be modular, we 
do not want to hard-code the order in 
which the tactics should be applied. Consequently,
we do not want to use in the orchestrator 
the pattern matching from `Ltac` or `Ltac2` to 
trigger the tactic. Otherwise, each new tactic 
added to the list may change the code of the 
orchestrator. 

But why is it not possible to use this 
pattern matching within the tactic? 
The problem is that each tactic will scan 
the local context separately, 
causing a drop in performance. Sometimes, 
we know that the next tactic should apply on 
newly generated hypothesis only. 
In addition, we may need a low-level pattern 
matching in some cases.

The trigger language is a way to free from 
`Ltac` or `Ltac2`'s constraints. 

## What does it consist on? 

The atomic bricks are the trigger variables, they
can be the goal or some hypothesis. 
They can have a certain form 
(conjunction, disjunction...), and these 
triggers can be combined together.

## Call of the orchestrator

You can parametrize the orchestrator tactic 
with the tactics and their triggers, 
and then it will do the job automatically
whenever you run
```orchestrator.```
in `Ltac1` proof mode.



