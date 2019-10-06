%%%%%%%%%%%%%%%%%%%
% File: warehouse.lp: Automated Warehouse
%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% sort and object declaration
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pair(1..n,1..n).
boolean(t;f).
validMoves(X,Y) :- X=-1..1, Y=-1..1, |X-Y| = 1.
maxUnits(U) :- U=1..100.

robot(R) :- init(object(robot,R),value(at,pair(X,Y))).
shelf(S) :- init(object(shelf,S),value(at,pair(X,Y))).
product(I) :- init(object(product,I),value(on,pair(S,U))).
order(O) :- init(object(order,O),value(line,pair(I,U))).

node(N,X,Y) :- init(object(node,N),value(at,pair(X,Y))).
highway(H,X,Y) :- init(object(highway,H),value(at,pair(X,Y))).
pickingStation(P,X,Y) :- init(object(pickingStation,P),value(at,pair(X,Y))).
robot(R,X,Y,0) :- init(object(robot,R),value(at,pair(X,Y))).
shelf(S,X,Y,0) :- init(object(shelf,S),value(at,pair(X,Y))).
product(I,S,U,0) :- init(object(product,I),value(on,pair(S,U))).
order(O,I,U,0) :- init(object(order,O),value(line,pair(I,U))).
order(O,P) :- init(object(order,O),value(pickingStation,P)).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% state description
%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% effect and preconditions of action
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%------------------------------------------------ move Action --------------------------------------------------
% For any R, there can be only one move at T
1{move(R,DX,DY,T):validMoves(DX,DY)}1 :- robot(R,X,Y,T), T=0..m-1.

% Move R to new location
robot(R,X+DX,Y+DY,T+1) :- move(R,DX,DY,T),robot(R,X,Y,T),node(N,X+DX,Y+DY),T=0..m.

% No move without a node at x+dx
:- move(R,DX,DY,T),robot(R,X,Y,T),0{node(N,X+DX,Y+DY)}0, T=0..m.

% A robot can only be at one place at a given time
:-  2{robot(R,X,Y,T):pair(X,Y)}, robot(R), T=0..m.
:- robot(R,X,Y,T), not 1{node(N,X,Y)}, T=0..m.

% When the robot moves and it carries a shelf, the the shelf should also move
shelf(S,X+DX,Y+DY,T+1) :- move(R,DX,DY,T),robot(R,X,Y,T),carries(R,T,t),shelf(S,X,Y,T),node(N,X+DX,Y+DY), T=0..m.

%------------------------------------------------ pickUp Action ------------------------------------------------
%If R and S at same location and pickUp implies carries is true
carries(R,T+1,t) :- robot(R,X,Y,T),shelf(S,X,Y,T),carries(R,T,f),pickUp(R,T),T=0..m.

%no pickup if no robot and no shelf at x,y at T
:- pickUp(R,T), robot(R,X,Y,T), carries(R,T,t),T=0..m.
:- pickUp(R,T), robot(R,X,Y,T), 0{shelf(S,X,Y,T)}0,T=0..m.

%------------------------------------------------ deliver Action ------------------------------------------------
% Deliver
order(O,I,UO-UD,T+1) :- deliver(R,O,I,UD,T), pickingStation(P,X,Y), order(O,P), order(O,I,UO,T), robot(R,X,Y,T), carries(R,T,t), shelf(S,X,Y,T), product(I,S,US,T), UD<=UO, UD<=US, T=1..m-1.
%product(I,S,US-UD,T+1) :- deliver(R,O,I,UD,T), pickingStation(P,X,Y), order(O,P), order(O,I,UO,T), robot(R,X,Y,T), carries(R,T,t), shelf(S,X,Y,T), product(I,S,US,T), UD<=UO, UD<=US, T=1..m-1.

%------------------------------------------------ Other Action Conditions --------------------------------------

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% domain independent axioms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% fluents are initially exogenous
1{robot(R,X,Y,0):pair(X,Y)}1 :- robot(R).
1{carries(R,T,f)}1 :-  robot(R,X,Y,T),T=0.
1{order(O,I,U,0):product(I), maxUnits(U)}1 :- order(O).
%1{product(I,S,U,0):maxUnits(U), shelf(S)}1 :- product(I).


% uniqueness and existence of value constraints
:- not 1{robot(R,X,Y,T)}1,  robot(R,X,Y,T),  T=0..m.
:- not 1{shelf(S,X,Y,T)}1, shelf(S), T=1..m.
:- not 1{product(I,S,U,T)}1, product(I), T=0..m.
:- not 1{order(O,I,U,T)}1, order(O,P), T=0..m.
:- not 1{carries(R,T,B):boolean(B)}1, robot(R,X,Y,T),  T=0..m.


%% actions are exogenous
{move(R,DX,DY,T)} :- robot(R), T=0..m-1, DX=-1..1, DY=-1..1, |DX+DY|=1.
{pickUp(R,T)} :- robot(R), T=0..m-1.
{deliver(R,O,I,UD,T)} :- robot(R,X,Y,T), order(O,I,UO,T),product(I,S,US,T), T=0..m-1, UD=1..US.

%% commonsense law of inertia
{robot(R,X,Y,T+1)} :- robot(R,X,Y,T), T<m.
{shelf(S,X,Y,T+1)} :- shelf(S,X,Y,T), T<m.
{product(I,S,U,T+1)} :- product(I,S,U,T), T<m.
{order(O,I,U,T+1)} :- order(O,I,U,T), T<m.
{carries(R,T+1,B)} :- carries(R,T,B), T<m.

%Goal
:- not order(2,2,0,m).

occurs(object(robot,R),move(X,Y),T) :- move(R,X,Y,T).
occurs(object(robot,R),pickUp,T) :- pickUp(R,T).
%occurs(object(robot,R),putDown,T) :- putDown(R,T).
occurs(object(robot,R),deliver(O,I,U),T) :- deliver(R,O,I,U,T).

%#show move/4.
#show robot/4.
%#show move/4.
%#show pickUp/2.
#show shelf/4.
#show carries/3.
#show order/4.
%#show order/2.
%#show product/4.
%#show product/1.
%#show pickingStation/3.
%#show deliver/5.
%#show delivered/1.
#show occurs/3.
