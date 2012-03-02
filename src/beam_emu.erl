%%% File    : beam_emu.erl
%%% Author  : Tony Rogvall <tony@iMac.local>
%%% Description : BEAM interpreter
%%% Created : 10 Jan 2006 by Tony Rogvall <tony@iMac.local>

-module(beam_emu).

%%
%% Simple API to call a emulated function
%%
-export([run/3]).

%% Internal API to dicover the meta level ;-)
-export([level/0, level0/0]).

%%
%% Instruction set. The first argument is the Beam Instruction State
%% then the instruction arguments (so -1 on arity to the orgininal)
%%
-export([func_info/4, int_code_end/1,
	 call/3, call_last/4, call_only/3, call_ext/3, call_ext_last/4,
	 bif/5,	 allocate/3, allocate_heap/4, allocate_zero/3,
	 allocate_heap_zero/4, test_heap/3,  init/2,
	 deallocate/2, return/1,
	 send/1, remove_message/1, timeout/1, loop_rec/3, loop_rec_end/2,
	 wait/2, wait_timeout/3]).
-export([m_plus/5, m_minus/5, m_times/5, m_div/5,
	 int_div/5, int_rem/5, int_band/5, int_bor/5, int_bxor/5,
	 int_bsl/5, int_bsr/5, int_bnot/4]).
-export([is_lt/4, is_ge/4, is_eq/4, is_ne/4, is_eq_exact/4, is_ne_exact/4,
	 is_integer/3, is_float/3, is_number/3, is_atom/3, is_pid/3,
	 is_reference/3, is_port/3, is_nil/3, is_binary/3,
	 is_list/3, is_nonempty_list/3, is_tuple/3,
	 test_arity/4, select_val/4, select_tuple_arity/4,
	 jump/2, 'catch'/3, catch_end/2, move/3,
	 get_list/4, get_tuple_element/4, set_tuple_element/4,
	 put_string/4, put_list/4, put_tuple/3, put/2,
	 badmatch/2, if_end/1, case_end/2, call_fun/2,
	 is_function/3, call_ext_only/3]).
-export([bs_put_integer/6, bs_put_binary/6, bs_put_float/6, 
	 bs_put_string/3, bs_need_buf/2]).
-export([fclearerror/1, fcheckerror/2]).
-export([fmove/3, fconv/3, fadd/5, fsub/5, fmul/5, fdiv/5, fnegate/4]).
-export([make_fun2/1, 'try'/3, try_end/2, try_case/2, try_case_end/2,
	 raise/3]).
-export([bs_init2/7, bs_bits_to_bytes/4, bs_add/4]).
-export([apply/2, apply_last/3]).
-export([is_boolean/3, is_function2/4]).
-export([bs_skip_bits2/6]).
-export([gc_bif/6]).
-export([is_bitstr/3]).
	 
	 
-import(lists, [map/2, foldr/3, reverse/1]).

-define(blank, '\0').

-define(BSF_ALIGNED, 1).
-define(BSF_LITTLE,  2).
-define(BSF_SIGNED,  4).
-define(BSF_EXACT,   8).
-define(BSF_NATIVE,  16).

%%
%% @type beam_state() = term()
%% @type arity() = non_negative_integer()
%% @type label() = {'f',non_negative_integer()}
%% @type void() = term()
%% @type register() = term()
%%
-record(s,
	{  x,
	   y,
	   f,
	   cp,       %% continuation pointer
	   i,        %% instruction pointer
	   code,     %% current code block
	   cs=[],    %% catch stack 
	   ferror,   %% floating point error code...
	   timer,    %% timeout timer
	   tuple_dst,
	   tuple_arity = 0,
	   tuple_data = [],
	   br,          %% destination bit/binary reg
	   bb = <<>>    %% binary buffer
	  }).



%%
%% @spec func_info(_S::beam_state(),Module::atom(),F::atom(),
%%                 Arity::non_neg_integer()) -> void()
%% 
%% @doc opcode=2
%%   Function information block
%%
func_info(S, M,F,Arity) ->
    fail(S#s { i=S#s.i+2},{f,0},error,{function_clause,M,F,Arity}).
%%
%% @spec int_code_end(_S::beam_state())  -> void()
%%
%% @doc opcode=3
%%   End interpreted code
%%
int_code_end(S) ->
    next(S).

%%
%% @spec call(_S::beam_state(), Arity::arity(),Label::label()) -> void()
%%
%% @doc opcode=4
%%
call(S, Arity, {f,I}) ->
    Ys = [S#s.i+1 | S#s.y],
    dispatch(S#s { i=I, y=Ys}).

%%
%% @spec call_last(_S::beam_state,Arity::arity(),Label::label(),Dealloc::non_negative_integer()) -> void()
%%
%% @doc opcode=5
%%
call_last(S, Arity, {f,I}, Dealloc) ->
    Ys = deallocate_(Dealloc, S#s.y),
    dispatch(S#s { i=I, y=Ys}).

%%
%% @doc opcode=6
%%
call_only(S, Arity,{f,I1}) ->
    dispatch(S#s { i=I1}).

%%
%% @doc opcode=7
%% @todo 
%%   Check if the module is beam interpreted then 
%%   and pass context, push code together with the return position.
%%
call_ext(S, Arity,{extfunc,Mod,Fun,Arity}) ->
    call_ext_(S, Mod,Fun,Arity).

%%
%% @doc opcode=8
%%
call_ext_last(S, Arity,{extfunc,Mod,Fun,Arity},Dealloc) ->
    call_ext_last_(S, Mod,Fun,Arity,Dealloc).

%%
%% @doc opcode=9
%%
bif(S, Bif,nofail,[],Dst) ->
    Val = apply(erlang,Bif,[]),
    next(store(Dst,Val,S));

%%
%% @doc opcode=10
%%
bif(S,Bif,Fail,[A1],Dst) ->
    case catch apply(erlang,Bif,[fetch(A1,S)]) of
	{'EXIT',Reason} ->
	    fail(S, Fail,exit,Reason);
	Val ->
	    next(store(Dst,Val,S))
    end;
%%
%% @doc opcode=11
%%
bif(S,Bif,Fail,[A1,A2],Dst) ->
    case catch apply(erlang,Bif,[fetch(A1,S),fetch(A2,S)]) of
	{'EXIT',Reason} ->
	    fail(S, Fail,exit,Reason);
	Val ->
	    next(store(Dst,Val,S))
    end.

%%	
%% @doc opcode=12
%%
allocate(S, StackNeed,_Live) ->
    %% FIXME: maybe kill some regs
    Ys = allocate_(StackNeed,[],S#s.y),
    next(S#s { y = Ys }).

%%
%% @doc opcode=13
%%
allocate_heap(S, StackNeed,_HeapNeed,_Live) ->
    %% FIXME: maybe kill some regs
    Ys = allocate_(StackNeed,[],S#s.y),
    next(S#s { y = Ys }).

%%
%% @doc opcode=14
%%
allocate_zero(S,StackNeed,_Live) ->
    %% FIXME: maybe kill some regs
    Ys = allocate_(StackNeed,?blank,S#s.y),
    next(S#s { y = Ys }).

%% @doc opcode=15	    
allocate_heap_zero(S,StackNeed,_HeapNeed,_Live) ->
    %% FIXME: maybe kill some regs
    Ys = allocate_(StackNeed,?blank,S#s.y),
    next(S#s { y = Ys }).
	
%% @doc opcode=16
test_heap(S,{alloc,[{words,_N},{floats,_F}]},_Live) ->
    %% FIXME: emulate this better
    %% heap and float are dynamic
    next(S);
%%
%% @doc opcode=16
%%
test_heap(S,_HeapNeed,_Live) ->
    %% FIXME: emulate this better
    %% heap is dynamic
    next(S).
%%
%% @doc opcode=17
%%
init(S,Dst) ->
    next(make_blank(Dst,S)).
%%
%% @doc opcode=18
%%
deallocate(S,Deallocate) ->
    Ys = deallocate_(Deallocate, S#s.y),
    next(S#s { y = Ys }).

%%
%% @doc opcode=19
%%   return value
%% @todo check if IRet is on form {Pos,Code} then install the code!
%%
return(S) ->
    case S#s.y of
	[IRet|Ys] ->
	    dispatch(S#s {i=IRet, y=Ys});
	[] ->
	    fetch({x,0},S)
    end.

%%
%% @doc opcode=20
%%
send(S) ->
    Result = (fetch({x,0},S) ! fetch({x,1},S)),
    S1 = store({x,0}, Result, S),
    next(S1).

%%
%% @doc opcode=21
%%
remove_message(S) ->
    message:remove(),
    next(S).

%%
%% @doc opcode=22
%%
timeout(S) ->
    message:first(), %% restart scanning
    next(S).

%%
%% @doc opcode=23
%%
loop_rec(S,{f,IL},Dst) ->
    case message:current() of
	empty ->
	    %% jump to wait or wait_timeout
	    dispatch(S#s { i=IL});
	{message,M} ->
	    next(store(Dst,M,S))
    end.

%%		
%% @doc opcode=24
%%
loop_rec_end(S,{f,IL}) ->
    Ignore = message:next(),
    dispatch(S#s {i=IL}).

%%
%% @doc opcode=25
%%
wait(S,{f,IL}) ->
    message:next(infinity),
    next(S#s {i=IL}).

%%
%% @doc opcode=26
%%
wait_timeout(S,{f,IL},Src) ->
    case S#s.timer of
	undefined ->
	    Tmo = fetch(Src,S),
	    if Tmo == infinity ->
		    message:next(),
		    dispatch(S#s {i=IL});
	       Tmo >= 0, Tmo =< 16#ffffffff ->
		    Timer = erlang:start_timer(Tmo,undefined,tmo),
		    case message:next(Tmo) of
			timeout ->
			    next(S);
			{message,_} ->
			    dispatch(S#s{i=IL,timer=Timer})
		    end;
	       true ->
		    fail(S,{f,0},error,timeout_value)
	    end;
	Timer ->
	    Timeout = case erlang:read_timer(Timer) of
			  false -> 0;
			  RVal -> RVal
		      end,
	    case message:next(Timeout) of
		timeout ->
		    next(S#s { timer=undefined });
		{message,_} ->
		    dispatch(S#s {i=IL})
	    end
    end.

%%
%% 27...38 not generated by compiler anymore? (but may be expanded?)

%%
%% @doc opcode=27
%%
m_plus(S,Fail,A1,A2,Reg) -> 
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A+B end).

%%
%% @doc opcode=28
%%
m_minus(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A-B end).

%%
%% @doc opcode=29
%%
m_times(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A*B end).

%%
%% @doc opcode=30
%%
m_div(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A / B end).

%%
%% @doc opcode=31
%%
int_div(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A div B end).

%%
%% @doc opcode=32
%%
int_rem(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A rem B end).

%%
%% @doc opcode=33
%%
int_band(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A band B end).

%%	
%% @doc opcode=34
%%
int_bor(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A bor B end).

%%
%% @doc opcode=35
%%
int_bxor(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A bxor B end).

%%
%% @doc opcode=36
%%
int_bsl(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A bsl B end).

%%
%% @doc opcode=37
%%
int_bsr(S,Fail,A1,A2,Reg) ->
    binary_op(S,Fail,A1,A2,Reg,fun(A,B) -> A bsr B end).

%%
%% @doc opcode=38
%%
int_bnot(S,Fail,A1,Reg) ->
    unary_op(S,Fail,A1,Reg,fun(A) -> bnot A end).

%%
%% @doc opcode=39 
%%
is_lt(S,Fail,A1,A2) -> 
    compare_op(S,Fail,A1,A2,fun(A,B) -> A < B end).


%%
%% @doc opcode=40
%%
is_ge(S,Fail,A1,A2) ->
    compare_op(S,Fail,A1,A2,fun(A,B) -> A >= B end).

%%
%% @doc opcode=41
%%
is_eq(S,Fail,A1,A2) ->
    compare_op(S,Fail,A1,A2,fun(A,B) -> A == B end).

%%
%% @doc opcode=42
%%
is_ne(S,Fail,A1,A2) ->
    compare_op(S,Fail,A1,A2,fun(A,B) -> A /= B end).

%%
%% @doc opcode=43
%%
is_eq_exact(S,Fail,A1,A2) ->
    compare_op(S,Fail,A1,A2,fun(A,B) -> A =:= B end).

%%
%% @doc opcode=44
%%
is_ne_exact(S,Fail,A1,A2) ->
    compare_op(S,Fail,A1,A2,fun(A,B) -> A =/= B end).

%%
%% @doc opcode=45
%%
is_integer(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_integer(A) end).

%%
%% @doc opcode=46
%%
is_float(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_float(A) end).

%% @doc opcode=47
is_number(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_number(A) end).


%% @doc opcode=48
is_atom(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_atom(A) end).

%% @doc opcode=49
is_pid(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_pid(A) end).

%% @doc opcode=50
is_reference(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_reference(A) end).

%% @doc opcode=51
is_port(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_port(A) end).


%% @doc opcode=52
is_nil(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> A =:= [] end).

%% @doc opcode=53
is_binary(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_binary(A) end).

%% @doc opcode=55
is_list(S,Fail,A1) ->
    test_op(S,Fail,A1,fun(A) -> is_list(A) end).

%% @doc opcode=56
is_nonempty_list(S,Fail,A1) ->
    test_op(S,Fail,A1,fun([_|_]) -> true;
			 (_) -> false end).
%%
%% @doc opcode=57
%%
is_tuple(S,Fail,A1) ->
    case is_tuple(fetch(A1,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.

%% @doc opcode=58 
%% @todo check size arg!
test_arity(S,Fail,Src,Size) ->
    Val = fetch(Src,S),
    if is_tuple(Val), size(Val) == Size ->
	    next(S);
       true -> fail(S,Fail)
    end.

%%
%% @doc opcode=59
%%
select_val(S,Val,Fail,{list,Pairs}) ->
    case select_val(fetch(Val,S), Pairs) of
	{f,I1} ->
	    dispatch(S#s{i=I1});
	false ->
	    fail(S,Fail)
    end.

%%
%% @doc opcode=60
%%
select_tuple_arity(S,Val,Fail,{list,Pairs}) ->
    T = fetch(Val, S),
    if is_tuple(T) ->
	    case select_val(size(T), Pairs) of
		{f,I1} ->
		    dispatch(S#s {i=I1});
		false ->
		    fail(S,Fail)
	    end;
       true ->
	    fail(S,Fail)
    end.

%%
%% @doc opcode=61
%%
jump(S,{f,I1}) ->
    dispatch(S#s{i=I1}).

%%
%% @spec catch(_S::beam_state(),Dst::register(),Fail::label()) -> void()
%%
%% @doc opcode=62
%%

'catch'(S,Dst,Fail) ->
    S1 = store(Dst,Fail,S),  %% just for the record
    Cs = [{Fail,length(S1#s.y)} | S1#s.cs],
    next(S1#s { cs = Cs }).

%%
%% @doc opcode=63
%%
catch_end(S,Dst) ->
	S1 = make_blank(Dst,S),  %% just for the record
	Cs = tl(S1#s.cs),
	X0 = fetch({x,0},S1),
	S2 = if X0 == ?blank ->
		     X1 = fetch({x,1},S1),
		     X2 = fetch({x,2},S1),
		     if X1 == thrown ->
			     store({x,0},X2,S1);
			X1 == error ->
			     store({x,0},{X2,[stack_trace]},S1);
			true ->
			     store({x,0},{'EXIT',X2},S1)
		     end;
		true ->
		     S1
	     end,
	next(S2#s { cs = Cs }).

%%
%% @doc opcode=64
%%
move(S,Src,Dst) ->
    S1 = store(Dst, fetch(Src,S), S),
    next(S1).

%%
%% @doc opcode=65
%%
get_list(S,Src,Head,Tail) ->
    [H|T] = fetch(Src,S),
    S1 = store(Head,H,S),
    S2 = store(Tail,T,S1),
    next(S2).

%%
%% @doc opcode=66
%%
get_tuple_element(S,Src,Ix,Dst) ->
    E = element(Ix+1, fetch(Src,S)),
    next(store(Dst,E,S)).

%%
%% @doc opcode=67
%%
set_tuple_element(S,Val,Dst,Ix) ->
    T = setelement(Ix,fetch(Dst,S),fetch(Val,S)),
    next(store(Dst,T,S)).

%%
%% @doc opcode=68
%%
put_string(S,Len,{string,String},Dst) ->
    next(store(Dst,String,S)).

%%
%% @doc opcode=69
%%
put_list(S,Head,Tail,Dst) ->
    L = [fetch(Head,S) | fetch(Tail,S)],
    next(store(Dst,L,S)).

%%
%% @doc opcode=70
%%
put_tuple(S,Arity,Dst) ->
    S1 =
	if Arity == 0 ->
		store(Dst,{},S);
	   true ->
		S#s { tuple_dst=Dst, tuple_arity=Arity, tuple_data=[]}
	end,
    next(S1).

%%
%% @doc opcode=71
%%
put(S,Src) ->
    Val = fetch(Src,S),
    Data = [Val | S#s.tuple_data],
    S1 = 
	case S#s.tuple_arity-1 of
	    0 -> 
		store(S#s.tuple_dst, list_to_tuple(reverse(Data)), 
		      S#s { tuple_dst=undefined, tuple_arity=0, tuple_data=[]});
	    A ->
		S#s { tuple_arity=A, tuple_data=Data }
	end,
    next(S1).

%%
%% @doc opcode=72 
%% @todo Check this
%%
badmatch(S,Fail) ->
    fail(S,Fail,error,badmatch).
%%	
%% @doc opcode=73 
%% @todo I++ ?
%%
if_end(S) ->
    fail(S,{f,0},error,if_clause).

%%
%% @doc opcode=74
%5
case_end(S,CaseVal) ->
    fail(S,{f,0},error,{case_clause,fetch(CaseVal,S)}).

%%
%% @doc opcode=75
%%
call_fun(S,Arity) ->
    As = fetch_regs(Arity,S),
    Fun = fetch({x,Arity},S),
    case catch erlang:apply(Fun, As) of
	{'EXIT',Reason} ->
	    fail(S,{f,0},exit,Reason);
	Ret ->
	    next(store({x,0}, Ret, S))
    end.

%%
%% @doc opcode=76
%%
make_fun(S, Arg1, Arg2, Arg3) ->
    {not_implemented, 76}.

%%
%% @doc opcode=77
%%
is_function(S,Fail,A1) ->
    case is_function(fetch(A1,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.

%%
%% @doc opcode=78
%%
call_ext_only(S,Arity,{extfunc,Mod,Fun,Arity}) ->
    call_ext_last_(S,Mod,Fun,Arity,0).

%% opcodes 79..88 not generated

%%
%% @doc opcode=79
%%
bs_start_match(S,Fail,Reg) ->
    {not_implemented,79}.
%%
%% @doc opcode=80
%%
bs_get_integer(S,Fail,[Arg,N,Flags,Dst]) ->
    {not_implemented,80}.
%%
%% @doc opcode=81
%%
bs_get_float(S,Fail,[Arg,N,Flags,Dst]) ->
    {not_implemented,81}.
%%
%% @doc opcode=82
%%
bs_get_binary(S,Fail,[Arg,N,Flags,Dst]) ->
    {not_implemented,82}.
%%
%% @doc opcode=83
%%
bs_skip_bits(S,Fail,[Arg,N,Flags]) ->
    {not_implemented,83}.
%%
%% @doc opcode=84
%%
bs_test_tail(S,Fail,[N]) ->
    {not_implemented,84}.
%%
%% @doc opcode=85
%%
bs_save(S,N) ->
    {not_implemented,85}.
%%
%% @doc opcode=86
%%
bs_restore(S,N) ->
    {not_implemented,86}.
%%
%% @doc opcode=87
%%
bs_init(S,N,Flags) ->
    {not_implemented,87}.
%%
%% @doc opcode=88
%%
bs_final(S,Fail,X) ->
    {not_implemented,88}.
%%
%% @doc opcode=89
%%
bs_put_integer(S,Fail,ArgSz,N,{field_flags,Flags},ArgInt) ->
    Int = fetch(ArgInt, S),
    Sz  = fetch(ArgSz, S),
    case catch (if Flags band ?BSF_LITTLE =/= 0 ->
			<<(S#s.bb)/bits, Int:Sz/little>>;
		   Flags band ?BSF_NATIVE =/= 0 ->
			<<(S#s.bb)/bits, Int:Sz/native>>;
		   true ->
			<<(S#s.bb)/bits, Int:Sz>>
		end) of
	       {'EXIT',Reason} ->
		 fail(S,Fail,exit,Reason);
	       BB ->
		 S1 = store(S#s.br, BB, S),
		 S2 = S1#s { bb = BB },
		 next(S2)
	 end.

%%
%% @doc opcode=90
%%
bs_put_binary(S,Fail,ArgSz,N,{field_flags,Flags},ArgBin) ->
    Bin = fetch(ArgBin, S),
    Sz  = fetch(ArgSz, S),
    case catch (if Flags band ?BSF_LITTLE =/= 0 ->
			<<(S#s.bb)/bits, Bin:Sz/binary-little>>;
		   Flags band ?BSF_NATIVE =/= 0 ->
			<<(S#s.bb)/bits, Bin:Sz/binary-native>>;
		   true ->
			<<(S#s.bb)/bits, Bin:Sz/binary>>
		end) of
	       {'EXIT',Reason} ->
		 fail(S,Fail,exit,Reason);
	       BB ->
		 S1 = store(S#s.br, BB, S),
		 S2 = S1#s { bb = BB },
		 next(S2)
	 end.

%%
%% @doc opcode=91
%%
bs_put_float(S,Fail,ArgSz,N,{field_flags,Flags},ArgFloat) ->
    Flt = fetch(ArgFloat, S),
    Sz  = fetch(ArgSz, S),
    case catch (if Flags band ?BSF_LITTLE =/= 0 ->
			<<(S#s.bb)/bits, Flt:Sz/little-float>>;
		   Flags band ?BSF_NATIVE =/= 0 ->
			<<(S#s.bb)/bits, Flt:Sz/native-float>>;
		   true ->
			<<(S#s.bb)/bits, Flt:Sz/float>>
		end) of
	       {'EXIT',Reason} ->
		 fail(S,Fail,exit,Reason);
	       BB ->
		 S1 = store(S#s.br, BB, S),
		 S2 = S1#s { bb = BB },
		 next(S2)
	 end.

%%
%% @doc opcode=92
%%
bs_put_string(S,Len,StrArg) ->
    String = fetch(StrArg, S),
    BB = <<(S#s.bb)/bits,(list_to_binary(String))/bits>>,
    S1 = store(S#s.br, BB, S),
    S2 = S1#s { bb = BB },
    next(S2).

%%
%% @doc opecode=93
%%
bs_need_buf(S,N) ->
    {not_implemented,93}.

%%
%% @doc opcode=94
%%
fclearerror(S) ->
    next(S#s { ferror=undefined}).

%% @doc opcode=95
fcheckerror(S,Fail) ->
    if S#s.ferror == undefined ->
	    next(S);
       true ->
	    fail(S,Fail,error,S#s.ferror)
    end.

%% @doc opcode=96
fmove(S,Src,FDst) ->
    S1 = store(FDst, fetch(Src,S), S),
    next(S1).
	
%% @doc opcode=97 
%% @todo Check the bignum conversion to float
fconv(S,Src,FDst) ->
    case fetch(Src, S) of
	Int when is_integer(Int) ->
	    next(store(FDst,float(Int),S));
	Float when is_float(Float) ->
	    next(store(FDst,Float,S));
	_ ->
	    fail(S,{f,0},error,badarith)
    end.

%% @doc opcode=98
fadd(S,_Fail,FA1,FA2,FDst) ->
    case catch (fetch(FA1,S) + fetch(FA2,S)) of
	{'EXIT',Reason} -> 
	    next(S#s { ferror=Reason});
	Val ->
	    next(store(FDst,Val,S))
    end.

%% @doc opcode=99
fsub(S,_Fail,FA1,FA2,FDst) ->
    case catch (fetch(FA1,S) - fetch(FA2,S)) of
	{'EXIT',Reason} -> 
	    next(S#s { ferror=Reason});
	Val ->
	    next(store(FDst,Val,S))
    end.

%% @doc opcode=100
fmul(S,_Fail,FA1,FA2,FDst) ->
    case catch (fetch(FA1,S) * fetch(FA2,S)) of
	{'EXIT',Reason} -> 
	    next(S#s { ferror=Reason });
	Val ->
	    next(store(FDst,Val,S))
    end.

%% @doc opcode=101
fdiv(S,_Fail,FA1,FA2,FDst) ->
    case catch (fetch(FA1,S) / fetch(FA2,S)) of
	{'EXIT',Reason} -> 
	    next(S#s { ferror=Reason});
	Val ->
	    next(store(FDst,Val,S))
    end.

%% @doc opcode=102 
fnegate(S,_Fail,FA1,FDst) ->
    case catch -fetch(FA1,S) of
	{'EXIT',Reason} -> 
	    next(S#s { ferror=Reason});
	Val ->
	    next(store(FDst,Val,S))
    end.

%% @doc opcode=103
make_fun2(S) ->
    {not_implemented,103}.

%% @doc opcode=104
'try'(S,Reg,Fail) ->
    {not_implemented,104}.

%% @doc opcode=105
try_end(S,Reg) ->
    {not_implemented,105}.

%% @doc opcode=106
try_case(S,Reg) ->
    {not_implemented,106}.

%% @doc opcode=107
try_case_end(S,Arg) ->
    {not_implemented,107}.

%% @doc opcode=108
raise(S,_Arg1,_Arg2) ->
    {not_implemented,108}.

%% @doc opcode=109
bs_init2(S,Fail,Src,W,R,{field_flags,Flags},Dst) ->
    S1 = S#s { br = Dst },
    next(S1).

%% @doc opcode=110
bs_bits_to_bytes(S,Fail,Src,Dst) ->
    {not_implemented,110}.

%% @doc opcode=111
bs_add(S,Fail,[Src1,Src2,Unit],Dest) ->
    Val = fetch(Src2,S)*Unit + fetch(Src1,S),
    next(store(Dest,Val,S)).
	
%% @doc opcode=112
apply(S,Arity) ->
    As = fetch_regs(Arity,S),
    Mod = fetch({x,Arity},S),
    Fun = fetch({x,Arity+1},S),
    case catch apply(Mod,Fun,As) of
	{'EXIT',Reason} ->
	    fail(S,{f,0},exit,Reason);
	Ret ->
	    next(store({x,0},Ret,S))
    end.

%% @doc opcode=113	    
apply_last(S,Arity,U) ->
    As = fetch_regs(Arity,S),
    Mod = fetch({x,Arity},S),
    Fun = fetch({x,Arity+1},S),
    case catch apply(Mod,Fun,As) of
	{'EXIT',Reason} ->
	    fail(S,{f,0},exit,Reason);
	Ret ->
	    case deallocate_(U, S#s.y) of
		[IRet|Ys] ->
		    S1 = S#s { y=Ys },
		    S2 = store({x,0},Ret,S1),
		    dispatch(S#s {i=IRet });
		[] ->
		    Ret  %% ?
	    end
    end.

%%
%% @doc opcode=114
%%
is_boolean(S,Fail,A1) ->
    case is_boolean(fetch(A1,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.
%%
%% @doc opcode=115
%%
is_function2(S,Fail,A1,A2) ->
    case is_function(fetch(A1,S),fetch(A2,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.
%%
%% @doc opcode=116
%%
bs_start_match2(S,Fail,Ctx,Live,Save,Dst) ->
    {not_implemented,116}.
%%
%% @doc opcode=117
%%
bs_get_integer2(S,Fail,Ctx,Live,Size,N,{field_flags,Flags},Dst) ->
    {not_implemented,117}.
%%
%% @doc opcode=118
%%
bs_get_float2(S,Fail,Ctx,Live,Size,N,{field_flags,Flags},Dst) ->
    {not_implemented,118}.
%%
%% @doc opcode=119
%%
bs_get_binary2(S, Fail,Ctx,Live,Size,N,{field_flags,Flags},Dst) ->
    {not_implemented,119}.
%%
%% @doc opcode=120
%%
bs_skip_bits2(S,Fail,CtxReg,SizeReg,Unit,{field_flags,0}) ->
    {not_implemented,120}.
%%
%% @doc opcode=121
%%
bs_test_tail2(S, Fail, Ctx, N) ->
    {not_implemented,121}.
%%
%% @doc opcode=122 
%%
bs_save2(S, Ctx, N) ->
    {not_implemented,122}.    
%%
%% @doc opcode=123 
%%
bs_restore2(S, Ctx, N) ->
    {not_implemented, 123}.
%%
%% @doc opcode=124
%%
gc_bif(S,Bif,Fail,Need,Args,Dst) ->
    case catch apply(erlang,Bif,fetch_args(Args,S)) of
	{'EXIT',Reason} ->
	    fail(S,Fail,exit,Reason);
	Val ->
	    next(store(Dst,Val,S))
    end.
%%
%% @doc opcode=126
%%
bs_final2(S, X, Y) ->
    {not_implemented, 126}.
%%
%% @doc opcode=127
%%
bs_bits_to_bytes2(S, A2,A3) ->
    {not_implemented, 127}.    
%%
%% @doc opcode=128
%%
put_literal(S, Index, Dst) ->
    {not_implemented, 128}.

%%
%% @doc opcode=129
%%
is_bitstr(S,Fail,A1) ->
    case is_bitstr(fetch(A1,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.
%%
%% @doc opcode=130
%%
bs_context_to_binary(S,Dst) ->
    {not_implemented, 130}.
%%
%% @doc opcode=131
%%
bs_test_unit(S,Fail,Ctx,N) ->
    {not_implemented, 131}.
%%
%% @doc opcode=132
%%
bs_match_string(S,Fail,Ctx,Bits,String) ->
    {not_implemented, 130}.
%%
%% @doc opcode=133
%%
bs_init_writable(S) ->
    {not_implemented, 133}.
%%
%% @doc opcode=134
%%
bs_append(S, Fail, Arg2, W, R, U, Arg6,{field_flags,Flags},Arg8) ->
    {not_implemented,134}.
%%
%% @doc opcode=135
%%
bs_private_append(S, Fail, Arg2, U, Arg4, {field_flags,Flags}, Arg6) ->
    {not_implemented,135}.
%%
%% @doc opcode=136
%%
trim(S,N,Remaining) ->
    {not_implemented,136}.
%%
%% @doc opcode=137
%%
bs_init_bits(S,Fail,Arg2,W,R,{field_flags,Flags},Arg6) ->
    {not_implemented,137}.
%%
%% @doc opcode=138
%%
bs_get_utf8(S, Fail, Arg2,Arg3,{field_flags,Flags},Arg4) ->
    {not_implemented,138}.
%%
%% @doc opcode=139
%%
bs_skip_utf8(S, Fail, Arg2, Arg3, {field_flags,Flags}) ->
    {not_implemented,139}.
%%
%% @doc opcode=140
%%
bs_get_utf16(S, Fail, Arg2,Arg3,{field_flags,Flags},Arg4) ->
    {not_implemented,140}.
%%
%% @doc opcode=141
%%
bs_skip_utf16(S, Fail, Arg2, Arg3, {field_flags,Flags}) ->
    {not_implemented,141}.
%%
%% @doc opcode=142
%%
bs_get_utf32(S, Fail, Arg2,Arg3,{field_flags,Flags},Arg4) ->
    {not_implemented,142}.
%%
%% @doc opcode=143
%%
bs_skip_utf32(S, Fail, Arg2, Arg3, {field_flags,Flags}) ->
    {not_implemented,143}.
%%
%% @doc opcode=144
%%
bs_utf8_size(S, Fail, Arg2, Arg3) ->
    {not_implemented,144}.
%%
%% @doc opcode=145
%%
bs_put_utf8(S, Fail, {field_flags,Flags},Arg3) ->
    {not_implemented,145}.
%%
%% @doc opcode=146
%%
bs_utf16_size(S, Fail, Arg2, Arg3) ->
    {not_implemented,146}.
%%
%% @doc opcode=147
%%
bs_put_utf16(S, Fail, {field_flags,Flags},Arg3) ->
    {not_implemented,147}.
%% @doc opcode=148
bs_put_utf32(S, Fail, {field_flags,Flags},Arg3) ->
    {not_implemented,148}.
%% @doc opcode=149
on_load(S) ->
    {not_implemented,149}.

%%
%% @spec run(Module::atom(), Function::atom(), Args::[term()]) -> term()
%%
%% @doc Execute an interpreted BEAM function
%%
run(Mod, F, Args) when is_atom(Mod), is_atom(F), is_list(Args) ->
    case beam_load:file(Mod) of
	{ok,{Mod,Exp,LCode}} ->
	    A = length(Args),
	    case lists:keysearch({F,A}, 1, Exp) of
		false -> erlang:error({undef,[{Mod,F,Args}]});
		{value,{_,I}} -> call_(I,LCode,Args)
	    end;
	{ok,{Mod1,Exp,LCode}} ->
	    erlang:error({load_error,Mod1});
	Error ->
	    erlang:error({load_error,Mod})
    end;
run(File, F, Args) when is_list(File), is_atom(F), is_list(Args) ->
    case beam_load:file(File) of
	{ok,{Mod,Exp,LCode}} ->
	    A = length(Args),
	    case lists:keysearch({F,A}, 1, Exp) of
		false -> erlang:error({undef,[{Mod,F,Args}]});
		{value,{_,I}} -> call_(I,LCode,Args)
	    end;
	Error ->
	    erlang:error({load_error,File})
    end.

%% @private
new_(Args) ->
    #s { x = list_to_tuple(Args),
	 f = {0.0, 0.0},
	 y = []
       }.

%% @private
call_(I, C, Args) ->
    init_(I, C, new_(Args)).

%% @private
init_(I, C) ->
    init_(I, C, new_([])).

%% @private
init_(I, C, S) ->
    dispatch(S#s { i=I, code=C }).

%% @private
next(S) ->
    dispatch(S#s { i=S#s.i + 1 }).

%% @private
%% dispatch the instruction 
dispatch(S) ->
    {Op,Args} = element(S#s.i, S#s.code),
    erlang:display({level(), S#s.i, {Op,Args}}),
    apply(?MODULE, Op, [S|Args]).

%%
%% @spec level() -> non_neg_integer()
%% @doc Return the meta BEAM meta level
%%
level() ->
    beam_emu:level0().

level0() ->
    0.

%% @private
unary_op(S,Fail,A1,Reg,Op) ->    
    case catch Op(fetch(A1,S)) of
	{'EXIT',Reason} -> 
	    fail(S,Fail,exit,Reason);
	Val ->
	    next(store(Reg,Val,S))
    end.

%% @private
binary_op(S,Fail,A1,A2,Reg,Op) ->
    case catch Op(fetch(A1,S),fetch(A2,S)) of
	{'EXIT',Reason} -> 
	    fail(S,Fail,exit,Reason);
	Val ->
	    next(store(Reg,Val,S))
    end.

%% @private
compare_op(S,Fail,A1,A2,Op) ->
    case Op(fetch(A1,S),fetch(A2,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.

%% @private
test_op(S,Fail,A1,Op) ->
    case Op(fetch(A1,S)) of
	false -> fail(S,Fail);
	true -> next(S)
    end.

%% @private    
call_ext_(S,erlang,'throw',1) ->
    fail(S,{f,0},thrown,fetch({x,0},S));
call_ext_(S,erlang,'exit',1) ->
    fail(S,{f,0},exit,fetch({x,0},S));
call_ext_(S,beam_emu,F,0) when F==level; F==level0 ->
    Ret = level()+1,
    next(store({x,0},Ret,S));
call_ext_(S,Mod,Fun,Arity) ->
    As = fetch_regs(Arity,S),
    case catch erlang:apply(Mod,Fun,As) of
	{'EXIT',Reason} ->
	    fail(S,{f,0},exit,Reason);
	Ret ->
	    next(store({x,0},Ret,S))
    end.

call_ext_last_(S,erlang,'throw',1,_Dealloc) ->
    fail(S,{f,0},thrown,fetch({x,0},S));
call_ext_last_(S,erlang,'exit',1,_Dealloc) ->
    fail(S,{f,0},exit,fetch({x,0},S));
call_ext_last_(S,beam_emu,F,0,Dealloc) when  F==level; F==level0 ->
    Ret = level()+1,
    case deallocate_(Dealloc, S#s.y) of
	[IRet|Ys] ->
	    S1 = S#s { y=Ys },
	    S2 = store({x,0},Ret,S1),
	    dispatch(S2#s { i=IRet});
	[] ->
	    Ret
    end;
call_ext_last_(S,Mod,Fun,Arity,Dealloc) ->
    As = fetch_regs(Arity,S),
    case catch apply(Mod,Fun,As) of
	{'EXIT',Reason} ->
	    fail(S,{f,0},exit,Reason);
	Ret ->
	    case deallocate_(Dealloc, S#s.y) of
		[IRet|Ys] ->
		    S1 = S#s { y=Ys },
		    S2 = store({x,0},Ret,S1),
		    dispatch(S2#s { i=IRet });
		[] ->
		    Ret
	    end
    end.

%% @private
fetch(Reg, State) ->
    Res = fetch_(Reg, State),
    io:format("fetch: ~w = ~p\n", [Reg, Res]),
    Res.

fetch_({x,I}, #s { x=X }) -> element(I+1, X);
fetch_({y,I}, #s { y=Y }) -> lists:nth(I+1,Y);
fetch_({fr,I}, #s { f=F }) -> element(I+1, F);
fetch_({atom,C},_S) -> C;
fetch_({integer,C},_S) -> C;
fetch_({float,C},_S) -> C;
fetch_(nil,_S) -> [];
fetch_({literal,Lit},_S) -> Lit;
fetch_({string,String},_S) -> String;
fetch_(Src, S) ->
    erlang:display({fetch,Src}),
    exit({function_clause,S}).

fetch_args([A|As], S) ->
    [fetch(A,S) | fetch_args(As,S)];
fetch_args([], _S) ->
    [].

%% fetch sequence of N registers {x,0} .. {x,N-1}
fetch_regs(0, S) ->    [];
fetch_regs(N, S) ->    fetch_regs(N-1, S, []).

fetch_regs(0, S, Regs) -> 
    [fetch({x,0},S)|Regs];
fetch_regs(I, S, Regs) ->
    fetch_regs(I-1,S,[fetch({x,I},S) | Regs]).

make_blank(Dst, S) ->
    store(Dst, ?blank, S).

store({x,I},Val,S=#s{x=X}) ->
    NX = size(X),
    if I >= NX ->
	    X1 = list_to_tuple(tuple_to_list(X)++fill((I+1)-NX,[],Val)),
	    S#s { x = X1 };
       true ->
	    S#s { x = setelement(I+1, X, Val) }
    end;
store({fr,I},Val,S=#s{f=F}) ->
    NF = size(F),
    if NF =< I ->
	    F1 = list_to_tuple(tuple_to_list(F)++fill((I+1)-NF,0.0,Val)),
	    S#s { f = F1 };
       true ->
	    S#s { f = setelement(I+1, F, Val) }
    end;
store({y,I}, Val, S=#s{y=Y}) ->
    S#s { y = set_nth_element(I, Y, Val) }.

%% @private
%% set nth element counting from 0!
set_nth_element(0, [H|T], V) -> [V|T];
set_nth_element(I, [H|T], V) -> [H | set_nth_element(I-1,T,V)].

%% @private
%% generate a lists of N nils (lists:duplicate!)
fill(N) ->
    fill(N,[],[]).

fill(0,_D,_V) -> [];
fill(1,_D,V) -> [V];
fill(I,D,V) -> [D | fill(I-1,D,V)].

%% @private
allocate_(0,_D,Ys) -> Ys;
allocate_(I,D,Ys) -> [D | allocate_(I-1,D,Ys)].

%% @private
deallocate_(0, Ys) -> Ys;
deallocate_(I, [_|Ys]) -> deallocate_(I-1, Ys).

%% @private
fail(S, {f,0}, Class, Reason) ->
    erlang:display({fail,Class,Reason}),
    case S#s.cs of
	[{{f,If},U0}|_] ->
	    U1 = length(S#s.y),
	    Ys = deallocate_(U1-U0, S#s.y),
	    S0 = store({x,0},?blank,S),
	    S1 = store({x,1},Class,S0),
	    S2 = store({x,2},Reason,S1),
	    dispatch(S#s { i=If, y=Ys });
	[] ->
	    if Class == thrown ->
		    exit(no_catch);
	       Class == exit ->
		    exit(Reason);
	       Class == error ->
		    exit({Reason,[stack_trace]})
	    end
    end;
fail(S, {f,I1},_Class,_Reason) ->
    dispatch(S#s { i=I1 }).

fail(S, {f,I1}) ->
    dispatch(S#s { i=I1 }).    


select_val(Val, [Val,Jump|_]) ->
    Jump;
select_val(Val, [{_,Val},Jump|_]) ->    
    Jump;
select_val(Val, [_,_|Select]) ->
    select_val(Val, Select);
select_val(_Val, []) ->
    false.
