%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2014, Tony Rogvall
%%% @doc
%%%    peek / remove message in message queue
%%% @end
%%% Created : 15 Feb 2014 by Tony Rogvall <tony@rogvall.se>

-module(message).

-export([first/0,
	 current/0,
	 next/0, 
	 next/1,
	 remove/0
	]).

%% @doc
%%    Restart message queue processing and return the first message
%%    or 'empty' if not message exist.
%% @end
-spec first() -> empty | {message,Message::term()}.	 

first() ->
    put('$msg',     empty),
    put('$msg_pos', -1),
    prim_eval:'receive'(fun(Message) ->
				case get('$msg') of
				    empty ->
					put('$msg_pos', 0),
					put('$msg',{message,Message}),
					nomatch;
				    _ ->
					nomatch
				end
			end, 0),
    get('$msg').

current() ->
    get('$msg').

-spec next() -> empty |  {message,Message::term()}.

next() ->
    next_(empty,0).

-spec next(T::timeout()) -> timeout | {message,Message::term()}.

next(Timeout) ->
    next_(timeout, Timeout).

next_(Default, Timeout) ->
    put('$msg', Default),
    set_message_pos_(2),
    prim_eval:'receive'(
      fun(Message) ->
	      case get('$msg_n')-1 of
		  -1 -> %% skip rest of messages
		      nomatch;
		  0 -> %% return next message
		      put('$msg_n', 0),
		      put('$msg_pos', get('$msg_pos')+1), %% advance pos
		      put('$msg',{message,Message}),
		      nomatch;
		  N ->
		      put('$msg_n', N),
		      nomatch
	      end
      end, Timeout),
    get('$msg').

%%
%% @doc
%%    Remove current message. Returns true if a message was
%%    removed, false otherwise
%% @end
%%
-spec remove() -> boolean().

remove() ->
    set_message_pos_(1),
    M = prim_eval:'receive'(
	  fun(_Message) ->
		  case get('$msg_n')-1 of
		      -1 -> %% skip rest of messages
			  nomatch;
		      0 -> %% return next message
			  put('$msg_n', 0),
			  true;
		      N ->
			  put('$msg_n', N),
			  nomatch
		  end
	  end, 0),
    if M =:= timeout -> false;
       true -> M
    end.

set_message_pos_(Offs) ->
    Pos = get_message_pos_(),
    put('$msg_pos',   Pos),
    put('$msg_n',     Pos+Offs).

get_message_pos_() ->
    case get('$msg_pos') of
	undefined -> 0;
	-1 -> 0;
	N -> N
    end.
	    
