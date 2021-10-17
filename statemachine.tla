---------------------------- MODULE statemachine ----------------------------
EXTENDS TLC, Sequences, Integers, Naturals

(* --algorithm statemachine
variables
    remoteAuthState = "NULL";

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
            webState := "RemoteAuthScreen";
        else 
            skip;        
        end if;
      
      RemoteAuthScreen:
        if webState = "RemoteAuthScreen" then
            
            remoteAuthState := "Undecided";
            
            either
               webState := "WebLoggedInScreen";
            or
               webState := "SmsScreen";
            end either;
        else
            skip;
        end if;                            
    
      SmsScreen:
        if webState = "SmsScreen" then
            remoteAuthState := "Cancelled";
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
            mobileState := "MobileLoginScreen";
        else
            skip;       
        end if;
        
      MobileLoginScreen:
        if mobileState = "MobileLoginScreen" then
            mobileState := "QueryRemoteAuthScreen";
        else
            skip;       
        end if;
        
      QueryRemoteAuthScreen:
        if mobileState = "QueryRemoteAuthScreen" then
            if remoteAuthState = "Undecided" then
                mobileState := "RemoteAuthDecisionScreen";
            else 
                mobileState := "MobileLoggedInScreen";
            end if;                                    
        else
            skip;
        end if;                            
    
      RemoteAuthDecisionScreen:
        if mobileState = "RemoteAuthDecisionScreen" then
            either
                mobileState := "GrantScreen";
            or
                mobileState := "RejectScreen";
            end either;
        else
            skip;
        end if;            
      
      GrantScreen:
        if mobileState = "GrantScreen" then
            assert remoteAuthState = "Undecided";
            remoteAuthState := "Granted";
            mobileState := "MobileLoggedInScreen";
        else
            skip;
        end if;                            
      
      RejectScreen:
        if mobileState = "RejectScreen" then
            assert remoteAuthState = "Undecided";
            remoteAuthState := "Rejected";
            mobileState := "MobileLoggedInScreen";
        else
            skip;
        end if;                            
    
      MobileLoggedInScreen:
        if mobileState = "MobileLoggedInScreen" then
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


\* BEGIN TRANSLATION (chksum(pcal) = "382f4ac5" /\ chksum(tla) = "5197a853")
\* Process variable run of process webProcess at line 11 col 5 changed to run_
VARIABLES remoteAuthState, pc, webState, run_, mobileState, run

vars == << remoteAuthState, pc, webState, run_, mobileState, run >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ remoteAuthState = "NULL"
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
     /\ UNCHANGED << remoteAuthState, webState, run_, mobileState, run >>

StartWebProcess == /\ pc[1] = "StartWebProcess"
                   /\ IF webState = "Start"
                         THEN /\ webState' = "WebLoginScreen"
                         ELSE /\ TRUE
                              /\ UNCHANGED webState
                   /\ pc' = [pc EXCEPT ![1] = "WebLoginScreen"]
                   /\ UNCHANGED << remoteAuthState, run_, mobileState, run >>

WebLoginScreen == /\ pc[1] = "WebLoginScreen"
                  /\ IF webState = "WebLoginScreen"
                        THEN /\ webState' = "RemoteAuthScreen"
                        ELSE /\ TRUE
                             /\ UNCHANGED webState
                  /\ pc' = [pc EXCEPT ![1] = "RemoteAuthScreen"]
                  /\ UNCHANGED << remoteAuthState, run_, mobileState, run >>

RemoteAuthScreen == /\ pc[1] = "RemoteAuthScreen"
                    /\ IF webState = "RemoteAuthScreen"
                          THEN /\ remoteAuthState' = "Undecided"
                               /\ \/ /\ webState' = "WebLoggedInScreen"
                                  \/ /\ webState' = "SmsScreen"
                          ELSE /\ TRUE
                               /\ UNCHANGED << remoteAuthState, webState >>
                    /\ pc' = [pc EXCEPT ![1] = "SmsScreen"]
                    /\ UNCHANGED << run_, mobileState, run >>

SmsScreen == /\ pc[1] = "SmsScreen"
             /\ IF webState = "SmsScreen"
                   THEN /\ remoteAuthState' = "Cancelled"
                        /\ webState' = "WebLoggedInScreen"
                   ELSE /\ TRUE
                        /\ UNCHANGED << remoteAuthState, webState >>
             /\ pc' = [pc EXCEPT ![1] = "WebLoggedInScreen"]
             /\ UNCHANGED << run_, mobileState, run >>

WebLoggedInScreen == /\ pc[1] = "WebLoggedInScreen"
                     /\ IF webState = "WebLoggedInScreen"
                           THEN /\ webState' = "Stop"
                           ELSE /\ TRUE
                                /\ UNCHANGED webState
                     /\ pc' = [pc EXCEPT ![1] = "StopWebProcess"]
                     /\ UNCHANGED << remoteAuthState, run_, mobileState, run >>

StopWebProcess == /\ pc[1] = "StopWebProcess"
                  /\ IF webState = "Stop"
                        THEN /\ run_' = FALSE
                        ELSE /\ TRUE
                             /\ run_' = run_
                  /\ pc' = [pc EXCEPT ![1] = "P"]
                  /\ UNCHANGED << remoteAuthState, webState, mobileState, run >>

webProcess == P \/ StartWebProcess \/ WebLoginScreen \/ RemoteAuthScreen
                 \/ SmsScreen \/ WebLoggedInScreen \/ StopWebProcess

P2 == /\ pc[2] = "P2"
      /\ IF run
            THEN /\ pc' = [pc EXCEPT ![2] = "StartMobileProcess"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
      /\ UNCHANGED << remoteAuthState, webState, run_, mobileState, run >>

StartMobileProcess == /\ pc[2] = "StartMobileProcess"
                      /\ IF mobileState = "Start"
                            THEN /\ mobileState' = "MobileLoginScreen"
                            ELSE /\ TRUE
                                 /\ UNCHANGED mobileState
                      /\ pc' = [pc EXCEPT ![2] = "MobileLoginScreen"]
                      /\ UNCHANGED << remoteAuthState, webState, run_, run >>

MobileLoginScreen == /\ pc[2] = "MobileLoginScreen"
                     /\ IF mobileState = "MobileLoginScreen"
                           THEN /\ mobileState' = "QueryRemoteAuthScreen"
                           ELSE /\ TRUE
                                /\ UNCHANGED mobileState
                     /\ pc' = [pc EXCEPT ![2] = "QueryRemoteAuthScreen"]
                     /\ UNCHANGED << remoteAuthState, webState, run_, run >>

QueryRemoteAuthScreen == /\ pc[2] = "QueryRemoteAuthScreen"
                         /\ IF mobileState = "QueryRemoteAuthScreen"
                               THEN /\ IF remoteAuthState = "Undecided"
                                          THEN /\ mobileState' = "RemoteAuthDecisionScreen"
                                          ELSE /\ mobileState' = "MobileLoggedInScreen"
                               ELSE /\ TRUE
                                    /\ UNCHANGED mobileState
                         /\ pc' = [pc EXCEPT ![2] = "RemoteAuthDecisionScreen"]
                         /\ UNCHANGED << remoteAuthState, webState, run_, run >>

RemoteAuthDecisionScreen == /\ pc[2] = "RemoteAuthDecisionScreen"
                            /\ IF mobileState = "RemoteAuthDecisionScreen"
                                  THEN /\ \/ /\ mobileState' = "GrantScreen"
                                          \/ /\ mobileState' = "RejectScreen"
                                  ELSE /\ TRUE
                                       /\ UNCHANGED mobileState
                            /\ pc' = [pc EXCEPT ![2] = "GrantScreen"]
                            /\ UNCHANGED << remoteAuthState, webState, run_, 
                                            run >>

GrantScreen == /\ pc[2] = "GrantScreen"
               /\ IF mobileState = "GrantScreen"
                     THEN /\ Assert(remoteAuthState = "Undecided", 
                                    "Failure of assertion at line 112, column 13.")
                          /\ remoteAuthState' = "Granted"
                          /\ mobileState' = "MobileLoggedInScreen"
                     ELSE /\ TRUE
                          /\ UNCHANGED << remoteAuthState, mobileState >>
               /\ pc' = [pc EXCEPT ![2] = "RejectScreen"]
               /\ UNCHANGED << webState, run_, run >>

RejectScreen == /\ pc[2] = "RejectScreen"
                /\ IF mobileState = "RejectScreen"
                      THEN /\ Assert(remoteAuthState = "Undecided", 
                                     "Failure of assertion at line 121, column 13.")
                           /\ remoteAuthState' = "Rejected"
                           /\ mobileState' = "MobileLoggedInScreen"
                      ELSE /\ TRUE
                           /\ UNCHANGED << remoteAuthState, mobileState >>
                /\ pc' = [pc EXCEPT ![2] = "MobileLoggedInScreen"]
                /\ UNCHANGED << webState, run_, run >>

MobileLoggedInScreen == /\ pc[2] = "MobileLoggedInScreen"
                        /\ IF mobileState = "MobileLoggedInScreen"
                              THEN /\ mobileState' = "Stop"
                              ELSE /\ TRUE
                                   /\ UNCHANGED mobileState
                        /\ pc' = [pc EXCEPT ![2] = "StopMobileProcess"]
                        /\ UNCHANGED << remoteAuthState, webState, run_, run >>

StopMobileProcess == /\ pc[2] = "StopMobileProcess"
                     /\ IF mobileState = "Stop"
                           THEN /\ run' = FALSE
                           ELSE /\ TRUE
                                /\ run' = run
                     /\ pc' = [pc EXCEPT ![2] = "P2"]
                     /\ UNCHANGED << remoteAuthState, webState, run_, 
                                     mobileState >>

mobileProcess == P2 \/ StartMobileProcess \/ MobileLoginScreen
                    \/ QueryRemoteAuthScreen \/ RemoteAuthDecisionScreen
                    \/ GrantScreen \/ RejectScreen \/ MobileLoggedInScreen
                    \/ StopMobileProcess

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
\* Last modified Sun Oct 17 10:27:35 CEST 2021 by zsolt
\* Created Sun Sep 26 07:46:17 CEST 2021 by zsolt
