%QUICK DESCRIPTION
% Most part of this model use fixed constraints.
% Objective is only focused on balancing, for each person, between the weight (i.e. number of festive days) of first-shift weeks and the weight of second-shift weeks he has been assigned to
% No balancing of heavy weeks (i.e. weeks with some extra festive day) across people
% No people coupling preferences (for example you could promote coupling based on different kind, morning or afternoon, of non-festive shifts)

%DATA DECLARATION
int: w;                                                             %number of weeks
set of int: WEEK=1..w;
array [WEEK] of int: w_holy;                                        %for each weeks, how many holydays it has
int: p;                                                             %number of persons 
set of int: PEOPLE=1..p;
array [PEOPLE] of int: p_done;                                      %for each person, the number of shifts totalized in past 
                                                                    %we have to consider that in order to balance the shifts to assign 
int: totdone=sum(p_done);                                           %total number of shifts already done in previous weeks
int: tottodo=sum(w_holy)*2;                                         %total number of shifts to assign (we need 2 for each holiday)
int: totshift=totdone+tottodo;                                      %total number of shifts
int: shiftpp=ceil(totshift/p);                                      %for each person max shifts bound (done and todo) 
int: totgap=shiftpp*p-totshift;                                     %total gap between shift assignable (from constraint) and total shifts
array [PEOPLE] of int:p_todo=[shiftpp - p_done[i] | i in PEOPLE];   %for each person, max shift to assign
array [PEOPLE] of set of WEEK: p_vaca;                              %for each person, his vacation weeks
array [PEOPLE] of set of WEEK: p_volu;                              %for each person, his voluntary weeks
int: wrest;                                                         %for all people, the mi number of rest-weeks after a shift 
int: wsmin;                                                         %not used
int: sXminpp=min(p_todo) div 2;
int: sXmaxpp=(max(p_todo)+1) div 2;
array [WEEK] of 0..1: w_heavy=[ if (w_holy[i] > 2 ) then 1 else 0 endif | i in WEEK];
int: totheavy=sum(w_heavy);

%DECISION VARIABLES
array [WEEK] of var PEOPLE: w_s1;                                   %for each week, who will do the first shift  
array [WEEK] of var PEOPLE: w_s2;                                   %for each week, who will do the second shift

%DEPENDENT VARIABLES
array [PEOPLE] of var sXminpp..sXmaxpp: p_load1;                    %for each person, how many first-shifts he will do
array [PEOPLE] of var sXminpp..sXmaxpp: p_load2;                    %for each person, how many second-shifts he will do
array [PEOPLE] of var 0..totheavy: p_heavy; 
var int: obj;                                                       %the objective

%CONSTRAINTS
include "bin_packing_capa.mzn";                                     %each person can be viewed as a bucket that cannot contain more holydays
constraint bin_packing_capa(p_todo, w_s1 ++ w_s2, w_holy ++ w_holy);%that his p_todo capacity
include "bin_packing_load.mzn";
constraint bin_packing_load(p_load1, w_s1, w_holy);                %for each person, just count the number of first-shift holydays assigned to that person  
constraint bin_packing_load(p_load2, w_s2, w_holy);                %for each person, just count the number of second-shift holydays assigned to that person  
include "global_cardinality.mzn";
constraint forall(pi in PEOPLE,wi in p_vaca[pi])(w_s1[wi] != pi /\ w_s2[wi] != pi);
                                                                    %for each person, respect his vacations!
constraint forall(pi in PEOPLE,wi in p_volu[pi])(w_s1[wi]  = pi \/ w_s2[wi]  = pi);
                                                                    %for each person, welcome his volunteering!                                                                    
include "alldifferent.mzn";                                         %for each person, at least wrest weeks of rest between 2 shifts 
constraint forall(i in 1..w-wrest) (alldifferent([ if j mod 2 == 0 
                                                    then w_s1[j div 2] 
                                                    else w_s2[j div 2] endif 
                                                 | j in i*2..(i+wrest)*2+1  ])) ;
constraint forall(i in PEOPLE) (p_heavy[i]=sum(j in WEEK where (w_s1[j] = i \/ w_s2[j] = i))(w_heavy[j]));
                                                 
%OBJECTIVE                                                          %for each person, the number of first-shift holidays and second-shift holidays
                                                                    %assigned to him must tend to be the same. A difference of max 1 is optimal.
constraint obj=sum(i in PEOPLE)(((p_load1[i] + p_load2[i]) div 2 )- min(p_load1[i],p_load2[i]));
                                                                    
                                                                                                                                                                                    
%SEARCH DIRECTIONS                                                  
solve :: int_search(                                                %search this way: w_s1[1], w_s2[1], w_s1[2], w_s2[2], ...
         [ if i mod 2 == 0 
             then w_s1[i div 2] 
             else w_s2[i div 2] endif 
         | i in 2..2*w+1 ], 
         input_order, indomain_min, complete)
      minimize obj;

%MODEL OUTPUT
output ["INPUT:"]++
       ["\n  p_done="]++[show(p_done)]++
       ["\n  p_todo="]++[show(p_todo)]++
       ["\n  w_holy="]++[show(w_holy)]++
       ["\n  p_vaca="]++[show(p_vaca)]++
       ["\n  p_volu="]++[show(p_volu)]++
       ["\n  wrest="]++[show(wrest)]++
       ["\nWHICH IMPLIES:"]++
       ["\n  totshift="]++[show(totshift)]++
       ["\n  shiftpp="]++[show(shiftpp)]++
       ["\n  totgap="]++[show(totgap)]++
       ["\n  sXminpp="]++[show(sXminpp)]++
       ["\n  sXmaxpp="]++[show(sXmaxpp)]++              
       ["\n  totheavy="]++[show(totheavy)]++
       ["\nOUTPUT:"]++       
       ["\n  w_s1="]++[show(w_s1)]++
       ["\n  w_s2="]++[show(w_s2)]++
       ["\nWHICH IMPLIES:"]++
       ["\n  p_load1="]++[show(p_load1)]++
       ["\n  p_load2="]++[show(p_load2)]++
       ["\n  p_loadgap="]++[show([p_todo[i]-p_load1[i]-p_load2[i] | i in PEOPLE])]++
       ["\n  p_heavy="]++[show(p_heavy)]++
       ["\n  obj="]++[show(obj)];
