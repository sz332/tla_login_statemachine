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

=============================================================================
