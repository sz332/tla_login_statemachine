---------------------------- MODULE statemachine ----------------------------
EXTENDS TLC, Sequences, Integers

(* --algorithm statemachine

variables
    accessAttemptState = "NULL";

fair process webProcess = 1
variables
    webState = "Start",
    run = TRUE;
begin P: 
  while run do
  
      StartWebProcess: 
        if webState = "Start" then
            webState := "WebLoginScreen";
        else
            skip;       
        end if;        
    
      WebLoginScreen:
        if webState = "WebLoginScreen" then
            webState := "TotpScreen";
        else 
            skip;        
        end if;

      TotpScreen:
        if webState = "TotpScreen" then
            either
               accessAttemptState := "Undecided";
               webState := "WebLoggedInScreen";
            or
              accessAttemptState := "Undecided";
               webState := "SmsScreen";
            end either;
        else
            skip;
        end if;                            
    
      SmsScreen:
        if webState = "SmsScreen" then
            accessAttemptState := "Cancelled";
            webState := "WebLoggedInScreen";       
        else
            skip;
        end if;
    
      WebLoggedInScreen:
        if webState = "WebLoggedInScreen" then
            webState := "Stop";
        else
            skip;
        end if;                            
    
      StopWebProcess:
        if webState = "Stop" then
            run := FALSE;
        else
            skip;        
        end if;
  end while;
end process;  


fair process mobileProcess = 2
variables
    mobileState = "Start",
    run = TRUE;

begin P2:
    while run do

      StartMobileProcess: 
        if mobileState = "Start" then
            mobileState := "AuthScreen";
        else
            skip;       
        end if;
        
      AuthScreen:
        if mobileState = "AuthScreen" then
            if accessAttemptState = "Undecided" then
                mobileState := "AccessAttemptScreen";
            else 
                mobileState := "MainScreen";
            end if;                                    
        else
            skip;
        end if;                            
    
      AccessAttemptScreen:
        if mobileState = "AccessAttemptScreen" then
            either
                assert accessAttemptState = "Undecided";
                mobileState := "GrantScreen";
            or
                assert accessAttemptState = "Undecided";
                mobileState := "RejectScreen";
            end either;
        else
            skip;
        end if;            
      
      GrantScreen:
        if mobileState = "GrantScreen" then
            accessAttemptState := "Granted";
            mobileState := "MainScreen";
        else
            skip;
        end if;                            
      

      RejectScreen:
        if mobileState = "RejectScreen" then
            accessAttemptState := "Rejected";
            mobileState := "MainScreen";
        else
            skip;
        end if;                            
    
      MainScreen:
        if mobileState = "MainScreen" then
            mobileState := "Stop";
        else
            skip;
        end if;                            
    
      StopMobileProcess:
        if mobileState = "Stop" then
            run := FALSE;
        else
            skip;        
        end if;
                
    end while;
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "8d39c6d1" /\ chksum(tla) = "4ac5da7d")
\* Process variable run of process webProcess at line 12 col 5 changed to run_
VARIABLES accessAttemptState, pc, webState, run_, mobileState, run

vars == << accessAttemptState, pc, webState, run_, mobileState, run >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ accessAttemptState = "NULL"
        (* Process webProcess *)
        /\ webState = "Start"
        /\ run_ = TRUE
        (* Process mobileProcess *)
        /\ mobileState = "Start"
        /\ run = TRUE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "P"
                                        [] self = 2 -> "P2"]

P == /\ pc[1] = "P"
     /\ IF run_
           THEN /\ pc' = [pc EXCEPT ![1] = "StartWebProcess"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << accessAttemptState, webState, run_, mobileState, run >>

StartWebProcess == /\ pc[1] = "StartWebProcess"
                   /\ IF webState = "Start"
                         THEN /\ webState' = "WebLoginScreen"
                         ELSE /\ TRUE
                              /\ UNCHANGED webState
                   /\ pc' = [pc EXCEPT ![1] = "WebLoginScreen"]
                   /\ UNCHANGED << accessAttemptState, run_, mobileState, run >>

WebLoginScreen == /\ pc[1] = "WebLoginScreen"
                  /\ IF webState = "WebLoginScreen"
                        THEN /\ webState' = "TotpScreen"
                        ELSE /\ TRUE
                             /\ UNCHANGED webState
                  /\ pc' = [pc EXCEPT ![1] = "TotpScreen"]
                  /\ UNCHANGED << accessAttemptState, run_, mobileState, run >>

TotpScreen == /\ pc[1] = "TotpScreen"
              /\ IF webState = "TotpScreen"
                    THEN /\ \/ /\ accessAttemptState' = "Undecided"
                               /\ webState' = "WebLoggedInScreen"
                            \/ /\ accessAttemptState' = "Undecided"
                               /\ webState' = "SmsScreen"
                    ELSE /\ TRUE
                         /\ UNCHANGED << accessAttemptState, webState >>
              /\ pc' = [pc EXCEPT ![1] = "SmsScreen"]
              /\ UNCHANGED << run_, mobileState, run >>

SmsScreen == /\ pc[1] = "SmsScreen"
             /\ IF webState = "SmsScreen"
                   THEN /\ accessAttemptState' = "Cancelled"
                        /\ webState' = "WebLoggedInScreen"
                   ELSE /\ TRUE
                        /\ UNCHANGED << accessAttemptState, webState >>
             /\ pc' = [pc EXCEPT ![1] = "WebLoggedInScreen"]
             /\ UNCHANGED << run_, mobileState, run >>

WebLoggedInScreen == /\ pc[1] = "WebLoggedInScreen"
                     /\ IF webState = "WebLoggedInScreen"
                           THEN /\ webState' = "Stop"
                           ELSE /\ TRUE
                                /\ UNCHANGED webState
                     /\ pc' = [pc EXCEPT ![1] = "StopWebProcess"]
                     /\ UNCHANGED << accessAttemptState, run_, mobileState, 
                                     run >>

StopWebProcess == /\ pc[1] = "StopWebProcess"
                  /\ IF webState = "Stop"
                        THEN /\ run_' = FALSE
                        ELSE /\ TRUE
                             /\ run_' = run_
                  /\ pc' = [pc EXCEPT ![1] = "P"]
                  /\ UNCHANGED << accessAttemptState, webState, mobileState, 
                                  run >>

webProcess == P \/ StartWebProcess \/ WebLoginScreen \/ TotpScreen
                 \/ SmsScreen \/ WebLoggedInScreen \/ StopWebProcess

P2 == /\ pc[2] = "P2"
      /\ IF run
            THEN /\ pc' = [pc EXCEPT ![2] = "StartMobileProcess"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << accessAttemptState, webState, run_, mobileState, run >>

StartMobileProcess == /\ pc[2] = "StartMobileProcess"
                      /\ IF mobileState = "Start"
                            THEN /\ mobileState' = "AuthScreen"
                            ELSE /\ TRUE
                                 /\ UNCHANGED mobileState
                      /\ pc' = [pc EXCEPT ![2] = "AuthScreen"]
                      /\ UNCHANGED << accessAttemptState, webState, run_, run >>

AuthScreen == /\ pc[2] = "AuthScreen"
              /\ IF mobileState = "AuthScreen"
                    THEN /\ IF accessAttemptState = "Undecided"
                               THEN /\ mobileState' = "AccessAttemptScreen"
                               ELSE /\ mobileState' = "MainScreen"
                    ELSE /\ TRUE
                         /\ UNCHANGED mobileState
              /\ pc' = [pc EXCEPT ![2] = "AccessAttemptScreen"]
              /\ UNCHANGED << accessAttemptState, webState, run_, run >>

AccessAttemptScreen == /\ pc[2] = "AccessAttemptScreen"
                       /\ IF mobileState = "AccessAttemptScreen"
                             THEN /\ \/ /\ Assert(accessAttemptState = "Undecided", 
                                                  "Failure of assertion at line 97, column 17.")
                                        /\ mobileState' = "GrantScreen"
                                     \/ /\ Assert(accessAttemptState = "Undecided", 
                                                  "Failure of assertion at line 100, column 17.")
                                        /\ mobileState' = "RejectScreen"
                             ELSE /\ TRUE
                                  /\ UNCHANGED mobileState
                       /\ pc' = [pc EXCEPT ![2] = "GrantScreen"]
                       /\ UNCHANGED << accessAttemptState, webState, run_, run >>

GrantScreen == /\ pc[2] = "GrantScreen"
               /\ IF mobileState = "GrantScreen"
                     THEN /\ accessAttemptState' = "Granted"
                          /\ mobileState' = "MainScreen"
                     ELSE /\ TRUE
                          /\ UNCHANGED << accessAttemptState, mobileState >>
               /\ pc' = [pc EXCEPT ![2] = "RejectScreen"]
               /\ UNCHANGED << webState, run_, run >>

RejectScreen == /\ pc[2] = "RejectScreen"
                /\ IF mobileState = "RejectScreen"
                      THEN /\ accessAttemptState' = "Rejected"
                           /\ mobileState' = "MainScreen"
                      ELSE /\ TRUE
                           /\ UNCHANGED << accessAttemptState, mobileState >>
                /\ pc' = [pc EXCEPT ![2] = "MainScreen"]
                /\ UNCHANGED << webState, run_, run >>

MainScreen == /\ pc[2] = "MainScreen"
              /\ IF mobileState = "MainScreen"
                    THEN /\ mobileState' = "Stop"
                    ELSE /\ TRUE
                         /\ UNCHANGED mobileState
              /\ pc' = [pc EXCEPT ![2] = "StopMobileProcess"]
              /\ UNCHANGED << accessAttemptState, webState, run_, run >>

StopMobileProcess == /\ pc[2] = "StopMobileProcess"
                     /\ IF mobileState = "Stop"
                           THEN /\ run' = FALSE
                           ELSE /\ TRUE
                                /\ run' = run
                     /\ pc' = [pc EXCEPT ![2] = "P2"]
                     /\ UNCHANGED << accessAttemptState, webState, run_, 
                                     mobileState >>

mobileProcess == P2 \/ StartMobileProcess \/ AuthScreen
                    \/ AccessAttemptScreen \/ GrantScreen \/ RejectScreen
                    \/ MainScreen \/ StopMobileProcess

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == webProcess \/ mobileProcess
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(webProcess)
        /\ WF_vars(mobileProcess)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Sep 26 11:58:38 CEST 2021 by zsolt
\* Created Sun Sep 26 07:46:17 CEST 2021 by zsolt
