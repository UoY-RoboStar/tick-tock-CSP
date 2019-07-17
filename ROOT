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

session "FL" in "FL" = HOL +
  description "Core FL model that excludes treatment of termination."
  sessions
     "Utils"
  theories
     Finite_Linear_Model
     Finite_Linear_Induction
     Finite_Linear_Tick_Param
     Finite_Linear_Priority
     Finite_Linear_Pri
     Finite_Linear_Pri_Laws
     Finite_Linear

session "TickTock-FL" in "TickTock-FL" = "FL" + 
  description "Galois connection results between TickTock and FL."
  sessions
     "TickTock"
  theories
     TickTock_Max
     TickTock_Max_FL
     TickTock_Max_Pri
     TickTock_Max_FL_Priority
     TickTock_Max_TT1
     TickTock_Max_TT1_Pri
     TickTock_FL
     TickTock_FL_Pri

session "Snippets-TickTock" in "TickTock" = "HOL" +
  options [
    document = "pdf",
    document_output = "generated"]
  theories
    TickTock_Core
  document_files
    build
