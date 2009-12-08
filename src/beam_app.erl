%%% File    : beam_app.erl
%%% Description : 
%%% Created : 26 Oct 2009 by Tony Rogvall <tony@PBook.local>

%%% @hidden
%%% @author Tony Rogvall <tony@rogvall.se>

-module(beam_app).

-behaviour(application).
-export([start/2,stop/1]).

%% start
start(_Type, _StartArgs) ->
    ok.

%% stop FIXME
stop(_State) ->
  ok.
