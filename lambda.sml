
datatype LEXP =  APP of LEXP * LEXP | LAM of string *  LEXP |  ID of string;

val vx = (ID "x");
val vy = (ID "y");
val vz = (ID "z");
val t1 = (LAM("x",vx));
val t2 = (LAM("y",vx));
val t3 = (APP(APP(t1,t2),vz));
val t4 = (APP(t1,vz));
val t5 = (APP(t3,t3));
val t6 = (LAM("x",(LAM("y",(LAM("z",(APP(APP(vx,vz),(APP(vy,vz))))))))));
val t7 = (APP(APP(t6,t1),t1));
val t8 = (LAM("z", (APP(vz,(APP(t1,vz))))));
val t9 = (APP(t8,t3));

(*---------------------------Item notation---------------------------*)

datatype IEXP = IAPP of IEXP * IEXP | ILAM of string *  IEXP |  IID of string;

val ivx = (IID "x");
val ivy = (IID "y");
val ivz = (IID "z");
val it1 = (ILAM("x",ivx));
val it2 = (ILAM("y",ivx));
val it3 = (IAPP(ivz,(IAPP(it2,it1))));
val it4 = (IAPP(ivz,it1));
val it5 = (IAPP(it3,it3));
val it6 = (ILAM("x",(ILAM("y",(ILAM("z",(IAPP(IAPP(ivz,ivy),(IAPP(ivz,ivx))))))))));
val it7 = (IAPP(it1,IAPP(it1,it6)));
val it8 = (ILAM("z", (IAPP((IAPP(ivz,it1),ivz)))));
val it9 = (IAPP(it8,it3));

fun printIEXP (IID v) = print v
|	  printIEXP (ILAM (v,e)) = (print "[";
	  print v;
	  print "]";
	  printIEXP e)
|     printIEXP (IAPP(e1,e2)) = (print "<"; 
 printIEXP e1;
 print ">";
 printIEXP e2);
 
 (*--------------------------De Bruijn----------------------------*)
 
datatype BEXP = BAPP of BEXP * BEXP | BLAM of BEXP |  BID of int;
 
val bv1 = (BID 1);
val bv2 = (BID 2);
val bv3 = (BID 3);
val bt1 = (BLAM(bv1));
val bt2 = (BLAM(bv2));
val bt3 = (BAPP(BAPP(bt1,bt2), bv3));
val bt4 = (BAPP(bt1,bv3));
val bt5 = (BAPP(bt3,bt3));
val bt6 = (BLAM((BLAM((BLAM((BAPP
            (BAPP(bv3,bv1),(BAPP(bv2,bv1))))))))));
val bt7 = (BAPP(BAPP(bt6,bt1),bt1));
val bt8 = (BLAM((BAPP(bv1,(BAPP(bt1,bv1))))));
val bt9 = (BAPP(bt8,bt3));

fun printBEXP (BID v) = print (Int.toString v)
|     printBEXP (BLAM (e)) = (print "(\\";
	  printBEXP e;
	  print ")")
| 	  printBEXP (BAPP(e1,e2)) = (print "(";
 	  printBEXP e1;
 	  print " ";
 	  printBEXP e2;
 	  print ")"); 
 	  
 (*--------------------------De Bruijn item-------------------*)
 	  
datatype IBEXP = IBAPP of IBEXP * IBEXP | IBLAM of IBEXP | IBID of int; 	  
 	  
val ibv1 = (IBID 1);
val ibv2 = (IBID 2);
val ibv3 = (IBID 3);
val ibt1 = (IBLAM(ibv1));
val ibt2 = (IBLAM(ibv2));
val ibt3 = (IBAPP(ibv3, IBAPP(ibt2, ibt1)));
val ibt4 = (IBAPP(ibv3,ibt1));
val ibt5 = (IBAPP(ibt3,ibt3));
val ibt6 = (IBLAM((IBLAM((IBLAM((IBAPP(IBAPP(ibv1,ibv2),(IBAPP(ibv1,ibv3))))))))));
val ibt7 = (IBAPP(ibt1, IBAPP(ibt1,ibt6)));
val ibt8 = (IBLAM((IBAPP((IBAPP(ibv1,ibt1)),ibv1))));
val ibt9 = (IBAPP(ibt3,ibt8)); 

fun printIBEXP (IBID v) = print (Int.toString v)
|	  printIBEXP (IBLAM (e)) = (print "[]";
	  printIBEXP e)
|     printIBEXP (IBAPP(e1,e2)) = (print "<"; 
 printIBEXP e1;
 print ">";
 printIBEXP e2);		
 
 (*---------------------Combinatory Logic--------------------*)  
 
datatype COM = CAPP of COM*COM | CID of string | CI | CK | CS;
  
val cvx = (CID "x");
val cvy = (CID "y");
val cvz = (CID "z");
val ct1 = (CI);
val ct2 = (CAPP(CK,cvx));
val ct3 = (CAPP(CAPP(ct1,ct2),cvz));
val ct4 = (CAPP(ct1,cvz));
val ct5 = (CAPP(ct3,ct3));
val ct6 = (CS);
val ct7 = (CAPP(CAPP(ct6,ct1),ct1));
val ct8 = (CAPP((CAPP(CS,CI)),CI));
val ct9 = (CAPP(ct8, ct3));

fun printCOM (CID v) = print v
|     printCOM (CI) = (print "I''")
|     printCOM (CS) = (print "S''")	  
|     printCOM (CK) = (print "K''")	 
| 	  printCOM (CAPP(e1,e2)) = (print "(";
 	  printCOM e1;
 	  print " ";
 	  printCOM e2;
 	  print ")");


 (*----------------Needed for beta reduction in M------------------*) 

(* checks whether a variable is free in a term *)
fun free id1 (ID id2) = if (id1 = id2) then  true else false|
    free id1 (APP(e1,e2))= (free id1 e1) orelse (free id1 e2) | 
    free id1 (LAM(id2, e1)) = if (id1 = id2) then false else (free id1 e1);

(* finds new variables which are fresh  in l and different from id*)   
fun findme id l = (let val id1 = id^"1"  in if not (List.exists (fn x => id1 = x) l) then id1 else (findme id1 l) end);

(* finds the list of free variables in a term *)
fun freeVars (ID id2)       = [id2]
  | freeVars (APP(e1,e2))   = freeVars e1 @ freeVars e2
  | freeVars (LAM(id2, e1)) = List.filter (fn x => not (x = id2)) (freeVars e1);


(*does substitution avoiding the capture of free variables*)
fun subs e id (ID id1) =  if id = id1 then e else (ID id1) |
    subs e id (APP(e1,e2)) = APP(subs e id e1, subs e id e2)|
    subs e id (LAM(id1,e1)) = (if id = id1 then LAM(id1,e1) else
                                   if (not (free id e1) orelse not (free id1 e))
				       then LAM(id1,subs e id e1)
                                   else (let val id2 = (findme id ([id1]@ (freeVars e) @ (freeVars e1)))
					 in LAM(id2, subs e id (subs (ID id2) id1 e1)) end));

(*Prints a term*)
fun printLEXP (ID v) =
    print v
  | printLEXP (LAM (v,e)) =
    (print "(\\";
     print v;
     print ".";
     printLEXP e;
     print ")")
  | printLEXP (APP(e1,e2)) =
    (print "(";
     printLEXP e1;
     print " ";
     printLEXP e2;
     print ")");

(*Finds a beta redex*)
fun is_redex (APP(LAM(_,_),_)) =
      true
  | is_redex _ =
      false;

fun is_var (ID id) =  true |
    is_var _ = false;

(*the function below adds lambda id to a list of terms *)
fun addlam id [] = [] |
    addlam id (e::l) = (LAM(id,e))::(addlam id l);

(*similar to above but adds app backward *)
fun addbackapp [] e2 = []|
    addbackapp (e1::l) e2 = (APP(e1,e2)):: (addbackapp l e2);

(*similar to above but adds app forward *)
fun addfrontapp e1 [] = []|
    addfrontapp e1  (e2::l) = (APP(e1,e2)):: (addfrontapp e1 l);

(*prints elements from a list putting an arrow in between*)
fun printlistreduce [] = ()|
    printlistreduce (e::[]) = (printLEXP e) |
    printlistreduce (e::l) = (printLEXP e; print "-->\n" ; (printlistreduce l));

(*beta-reduces a redex*)
fun red (APP(LAM(id,e1),e2)) = subs e2 id e1;


fun has_redex (ID id) = false |
    has_redex (LAM(id,e)) = has_redex e|
    has_redex (APP(e1,e2)) = if (is_redex  (APP(e1,e2))) then true else
                              ((has_redex e1) orelse (has_redex e2));

fun  one_rireduce (ID id) = (ID id)|
    one_rireduce (LAM(id,e)) = LAM(id, (one_rireduce e))|
    one_rireduce (APP(e1,e2)) = if (has_redex e2) then (APP(e1, (one_rireduce e2))) else
                                if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                          if (has_redex e1) then (APP((one_rireduce e1), e2)) else
                                              (APP(e1,e2));

fun one_loreduce (ID id) = (ID id)|
    one_loreduce (LAM(id,e)) = LAM(id, (one_loreduce e))|
    one_loreduce (APP(e1,e2)) = if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                 if (has_redex e1) then APP(one_loreduce e1, e2) else
                                 if (has_redex e2) then APP(e1, (one_loreduce e2)) else (APP(e1,e2));

findme   "x" ["x", "x1", "x11", "x111"];
   
 (*----------------Needed for translations to M''------------------*) 
 
 fun cfree id1 (CID id2) = if (id1 = id2) then true else false 
 |     cfree id1 (CAPP(e1,e2)) = (cfree id1 e1) orelse (cfree id1 e2) 
 |     cfree id1 (CI) = false 
 |     cfree id1 (CK) = false 
 |     cfree id1 (CS) = false; 
    
fun cfunf id (CID id1) = if id = id1 then CI 
              else CAPP(CK,(CID id1)) 
|     cfunf id (CAPP(e1,e2))= if not(cfree id (CAPP(e1,e2)))
               then CAPP(CK,CAPP(e1,e2))
               else if((CID id) = e2) andalso not(cfree id e1)
               then e1 else CAPP(CAPP(CS,(cfunf id e1)),(cfunf id e2))
|     cfunf id e = e ;
                  
(*------------------------Transl U (M to M'')----------------------*) 

fun toC (ID id) = (CID id) 
|     toC (LAM(id,e)) = cfunf id (toC e)
|     toC(APP(e1,e2)) = CAPP(toC e1, toC e2);

 (*-----------------------Transl V (M to M')------------------------*)                
                  
fun Itran (ID id) = (IID id)
|     Itran (APP(e1,e2)) = (IAPP((Itran e2),(Itran e1)))
|     Itran (LAM(id,e)) = (ILAM (id,(Itran e)));             

 (*---------------------Transl T (M' to M'')---------------------------*)   
 
fun ItoC (IID id) = (CID id) 
|     ItoC (ILAM(id,e)) = cfunf id (ItoC e)
|     ItoC (IAPP(e1,e2)) = CAPP(ItoC e2, ItoC e1);

 (*------------------------------Subterms M''-------------------------*)  
  
fun subterms(CID id)=[CID id] 
|     subterms(CK) = [CK] 
|     subterms(CI) = [CI] 
|     subterms(CS) = [CS] 
|    subterms(CAPP(e1,e2)) =  [CAPP(e1,e2)] @ (subterms e1) @ (subterms e2);


(*--------------------Beta reduction in COM---------------------------*)
 
 fun isCOMredex (CAPP(CI,_)) = true
 |     isCOMredex (CAPP(CAPP(CK,_),_)) = true
 |     isCOMredex (CAPP(CAPP(CAPP(CS,_),_),_)) = true
 |     isCOMredex _ = false;

fun hasCredex (CID id) = false 
|     hasCredex (CK)= false
|     hasCredex (CI)= false
|     hasCredex (CS)= false
|     hasCredex (CAPP(e1,e2)) = if (isCOMredex  (CAPP(e1,e2))) then true else
                                ((hasCredex e1) orelse (hasCredex e2));

fun cred (CAPP(CI,e1)) = e1 
|     cred (CAPP(CAPP(CK,e1),e2)) = e1 
|     cred (CAPP(CAPP(CAPP(CS,e1),e2),e3)) = (CAPP(CAPP(e1,e3),CAPP(e2,e3)))
|     cred e = e;

fun oneCreduce (CID id) = (CID id)
|     oneCreduce(CK)=(CK)
|     oneCreduce(CI)=(CI)
|     oneCreduce(CS)=(CS)
|     oneCreduce (CAPP(e1,e2)) = if (isCOMredex (CAPP(e1,e2))) 
    													then (cred (CAPP(e1,e2))) else
                            if (hasCredex e1) then CAPP(oneCreduce e1, e2) else
                            if (hasCredex e2) then CAPP(e1, (oneCreduce e2)) 
                            else (CAPP(e1,e2));

fun creduce(CID id)= [(CID id)] 
|     creduce(CK)=[(CK)]
|     creduce(CI)=[(CI)]
|     creduce(CS)=[(CS)]
|     creduce (CAPP(e1,e2)) = (let val l1 = if (isCOMredex (CAPP(e1,e2))) 
			then  (creduce (cred (CAPP(e1,e2)))) else 
            if (hasCredex e1) then (creduce (CAPP(oneCreduce e1, e2))) else 
            if (hasCredex e2) then  (creduce (CAPP(e1, (oneCreduce e2)))) else []
            in [CAPP(e1,e2)]@l1
            end);
   
fun printClistcreduce [] = ()
|     printClistcreduce (e::[]) = (printCOM e) 
|     printClistcreduce (e::l) = (printCOM e; print "-->\n" ; (printClistcreduce l));     
   
            
fun printCreduce e = (let val tmp =  (creduce e)
                             in printClistcreduce tmp end);

    
fun printSteps(e) = print (Int.toString((length e)-1));
            
fun printCreduce_andsteps e = (let val tmp =  (creduce e) 
		in (printClistcreduce tmp; print "\nNumber Of Steps: ";printSteps tmp;print"\n")
		end);              
		

(*------------------------------------eta-reduction in M---------------------------------------*) 

fun is_eta_redex (LAM(id,(APP( e1, e2)))) = if free id e1 then false 
											else (if (ID id) =  e2 then true else false)
|   is_eta_redex _ = false;

fun has_eta_redex (ID id) = false 
|   has_eta_redex (APP(e1,e2)) =  (has_eta_redex e1) orelse (has_eta_redex e2) 
|   has_eta_redex (LAM(id,e)) = if (is_eta_redex(LAM(id,e))) then true else (has_eta_redex e) ;         
           
fun ered (LAM(id,(APP(e1,e2)))) = e1
|     ered e = e;

fun one_eta_reduce (ID id) = (ID id)
|     one_eta_reduce (LAM(id,e)) = if (is_eta_redex (LAM(id,e))) then
                 (ered (LAM(id,e))) else LAM(id, (one_eta_reduce e))
|     one_eta_reduce (APP(e1,e2)) =  if (has_eta_redex e1) then 
				APP(one_eta_reduce e1, e2) else
			    if (has_eta_redex e2) then APP(e1, (one_eta_reduce e2)) 
			    else (APP(e1,e2));


fun etareduce (ID id) =  [(ID id)] 
|     etareduce (LAM(id,e)) = (let val l1 = if (is_eta_redex (LAM(id,e))) then  etareduce (ered (LAM(id,e))) else 
				 if (has_eta_redex e) then (etareduce (LAM(id, (one_eta_reduce e)))) else []
				 in [(LAM(id,e))]@l1
			      end) 
|     etareduce (APP(e1,e2)) = (let val l1 =  if (has_eta_redex e1) then (etareduce (APP(one_eta_reduce e1, e2))) else 
				 if (has_eta_redex e2) then  (etareduce (APP(e1, (one_eta_reduce e2)))) else []
				 in [APP(e1,e2)]@l1
			      end);
   
(*printing function*)    
fun print_eta_reduce e = (let val tmp =  (etareduce e)
	  in printlistreduce tmp end);
	  
(*--------------eta redexes-----------------*)  
  
val et1 = (LAM("x",APP(vy,vx)));
val et2 = (APP(et1,et1));
val et3 = (APP(et2,(LAM("z",(APP(et2,vz))))));
val et4 = (LAM("x",APP(et1,et1)));
val et5 = (APP(t1,et1));
val et6 = (LAM("z",LAM("y",(APP(vx,vy)))));
val et7 = (LAM ("x",(LAM ("z", LAM("y", (APP(ID "c",vy)))))));
val et8 = (LAM("x",(APP(t4,et1))));  

(*---------------------------------------------------*)     
                                 
 (*------------------------Omega----------------------*)                     

val OEXP = (APP((LAM("x",(APP(vx, vx)))), (LAM("x",(APP(vx, vx))))));
val OIEXP = (IAPP((ILAM("x",(IAPP(ivx, ivx)))),(ILAM("x",(IAPP(ivx, ivx))))));
val OBEXP = (BAPP((BLAM(BAPP(bv1, bv1))), (BLAM(BAPP(bv1, bv1)))));
val OIBEXP = (IBAPP ((IBLAM(IBAPP(ibv1, ibv1))), (IBLAM(IBAPP(ibv1, ibv1)))));
val OCOM  = (CAPP((CAPP(CAPP(CS, CI),(CI))), (CAPP(CAPP(CS, CI),(CI)))));     

(*-----------------leftReduce VS RightReduce----------------*)

fun LeftRed (ID id) =  [(ID id)] 
|     LeftRed (LAM(id,e)) = (addlam id (LeftRed e)) 
|     LeftRed (APP(e1,e2)) = (let val l1 = if (is_redex (APP(e1,e2))) then  (LeftRed (red (APP(e1,e2)))) else 
				 if (has_redex e1) then (LeftRed (APP(one_loreduce e1, e2))) else 
				 if (has_redex e2) then  (LeftRed (APP(e1, (one_loreduce e2)))) else []
				 in [APP(e1,e2)]@l1
			      end);


fun rightRed (ID id) =  [(ID id)] 
|     rightRed (LAM(id,e)) = (addlam id (rightRed e)) 
|     rightRed (APP(e1,e2)) = (let val l1 = if (has_redex e2) then  (rightRed (APP(e1, (one_rireduce e2)))) else 
				 if (is_redex (APP(e1,e2))) then  (rightRed (red (APP(e1,e2)))) else 
				 if (has_redex e1) then (rightRed (APP(one_rireduce e1, e2))) else []
				 in [APP(e1,e2)]@l1
			      end);
	
			    
fun print_left_reduce e = (let val tmp =  (LeftRed e)
		      in printlistreduce tmp end);	
		      
fun print_right_reduce e = (let val tmp =  (rightRed e)
		      in printlistreduce tmp end);			      
		      		    
			    
(*---------expressions to test left VS right---------*)		

val LR1 = (APP(t1,t1))	;
val LR2 = (APP((APP(t1,vy)),(APP((LAM("z",vy)),t1))));
val LR3 = (APP(t2,OEXP));
val LR4 = (APP(OEXP,t2));
val LR5 = (APP(t9,t1));
val LR6 = (APP(t4,t3));
            
