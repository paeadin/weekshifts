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
int: wsmin;                                                         %for all people, the minimum number of weeks assigned to him for each kind of shift  
                                                                    %this actually could be derived 
%DECISION VARIABLES
array [WEEK] of var PEOPLE: w_s1;                                   %for each week, who will do the first shift  
array [WEEK] of var PEOPLE: w_s2;                                   %for each week, who will do the second shift

%DEPENDENT VARIABLES
array [PEOPLE] of var 1..shiftpp: p_load;                           %for each person, how many shifts he will do
array [PEOPLE] of var wsmin..(w div p) +1: p_s1;                    %for each person, how many first-shift weeks he will do
array [PEOPLE] of var wsmin..(w div p) +1: p_s2;                    %for each person, how many second-shift weeks he will do
var int: obj;                                                       %the objective

%CONSTRAINTS
include "bin_packing_capa.mzn";                                     %each person can be viewed as a bucket that cannot contain more holydays
constraint bin_packing_capa(p_todo, w_s1 ++ w_s2, w_holy ++ w_holy);%than his p_todo capacity
include "bin_packing_load.mzn";
constraint bin_packing_load(p_load,w_s1 ++ w_s2, w_holy ++ w_holy); %for each person, just count the number of holydays assigned to that person  
include "global_cardinality.mzn";
constraint global_cardinality(w_s1,[i|i in PEOPLE],p_s1);           %for each person, just count the number of first-shift weeks he will do
constraint global_cardinality(w_s2,[i|i in PEOPLE],p_s2);           %for each person, just count the number of second-shift weeks he will do
constraint forall(pi in PEOPLE,wi in p_vaca[pi])(w_s1[wi] != pi /\ w_s2[wi] != pi);
                                                                    %for each person, respect his vacations!
constraint forall(pi in PEOPLE,wi in p_volu[pi])(w_s1[wi]  = pi \/ w_s2[wi]  = pi);
                                                                    %for each person, welcome his volunteering!                                                                    
include "alldifferent.mzn";                                         %for each person, at least wrest weeks of rest between 2 shifts 
constraint forall(i in 1..w-wrest) (alldifferent([ if j mod 2 == 0 
                                                    then w_s1[j div 2] 
                                                    else w_s2[j div 2] endif 
                                                 | j in i*2..(i+wrest)*2+1  ])) ;

%OBJECTIVE                                                          %for each person, the number of first-shift weeks and second-shift weeks
                                                                    %assigned to him must tend to be the same. A difference of max 1 is optimal.
constraint obj=sum(i in PEOPLE)(((p_s1[i] + p_s2[i]) div 2 )- min(p_s1[i],p_s2[i]));
                                                                    
%SEARCH DIRECTIONS                                                  
solve :: int_search(                                                %search this way: w_s1[1], w_s2[1], w_s1[2], w_s2[2], ...
         [ if i mod 2 == 0 
             then w_s1[i div 2] 
             else w_s2[i div 2] endif 
         | i in 2..2*w+1 ], 
         input_order, indomain_min, complete)
      minimize obj;

%MODEL OUTPUT
output ["\ntotshift="]++[show(totshift)]++
       ["\nshiftpp="]++[show(shiftpp)]++
       ["\np_done="]++[show(p_done)]++
       ["\np_vaca="]++[show(p_vaca)]++
       ["\ntotgap="]++[show(totgap)]++       
       ["\np_gap="]++[show([p_todo[i]-p_load[i] | i in PEOPLE])]++
       ["\np_todo="]++[show(p_todo)]++
       ["\np_s1="]++[show(p_s1)]++
       ["\np_s2="]++[show(p_s2)]++
       ["\nw_ho="]++[show(w_holy)]++
       ["\nw_s1="]++[show(w_s1)]++
       ["\nw_s2="]++[show(w_s2)]++
       ["\nobj="]++[show(obj)];
