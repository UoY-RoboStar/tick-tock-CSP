session "Utils" in "Utils" = HOL +
  description "Auxiliary theories."
  theories
    Event_Priority

session "TickTock" in "TickTock" = HOL +
  description "Core model and healthiness conditions of tick-tock."
  sessions
    "Utils"
  theories 
    TickTock_Core
    TickTock
    TickTock_Interrupt
    TickTock_Prioritise

session "FL" in "FL" = HOL +
  description "Core FL model that excludes treatment of termination."
  sessions
     "Utils"
  theories
     Finite_Linear_Model
     Finite_Linear_Induction
     Finite_Linear_Tick_Param
     Finite_Linear_Priority
     Finite_Linear

session "TickTock-FL" in "TickTock-FL" = "FL" + 
  description "Galois connection results between TickTock and FL."
  sessions
     "TickTock"
