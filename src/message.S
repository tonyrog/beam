{module, message}.  %% version = 0

{exports, [{first,0},
	   {next,0}, {next,1},
	   {remove,0},
	   {current,0},
	   {module_info,0},
	   {module_info,1}]}.

{attributes, []}.

{labels, 24}.

%%
%% first() -> empty | {message, M}
%%
%% Description:
%%   Restart message queue scanning and get the first message
%%   return 
%%
{function, first, 0, 2}.
{label,1}.
    {func_info,{atom,message},{atom,first},0}.
{label,2}.
    timeout.
    {loop_rec,{f,3},{x,0}}.
    {test_heap,3,1}.
    {put_tuple,2,{x,1}}.
    {put,{atom,message}}.
    {put,{x,0}}.
    {move,{x,1},{x,0}}.
    return.
{label,3}.
    {move,{atom,empty},{x,0}}.
    return.


%% 
%% next() ->  empty | {message, M}
%%
%% Description:
%%   Get the next message in the message queue
%%
{function, next, 0, 5}.
{label,4}.
    {func_info,{atom,message},{atom,next},0}.
{label,5}.
    {loop_rec,{f,7},{x,0}}.
%%    {jump,{f,8}}.  does not work, do a dummy
    {move,{atom,false},{x,0}}.
    {test,is_eq,{f,8},[{x,0},{atom,true}]}.
{label,6}.
    {loop_rec,{f,7},{x,0}}.
    {test_heap,3,1}.
    {put_tuple,2,{x,1}}.
    {put,{atom,message}}.
    {put,{x,0}}.
    {move,{x,1},{x,0}}.
    return.
{label,8}.
    {loop_rec_end,{f,6}}.
{label,7}.
    {move,{atom,empty},{x,0}}.
    return.

%%
%% current() -> empty | {message,M}
%%
%% Description:
%%    Peek the current message
%%
{function, current, 0, 10}.
{label,9}.
    {func_info,{atom,message},{atom,current},0}.
{label,10}.
    {loop_rec,{f,11},{x,0}}.
    {test_heap,3,1}.
    {put_tuple,2,{x,1}}.
    {put,{atom,message}}.
    {put,{x,0}}.
    {move,{x,1},{x,0}}.
    return.
{label,11}.
    {move,{atom,empty},{x,0}}.
    return.

%%
%% next(Tmo) -> timeout | {message,M}
%%
%% Description:
%%
%% Get the next message in the message queue
%% or wait for next message maximum Tmo millisecs
%%
{function, next, 1, 13}.
{label,12}.
    {func_info,{atom,message},{atom,next},1}.
{label,13}.
    {allocate,1,1}.
    {move,{x,0},{y,0}}.
    %% {'%live', 0}.
    %% Check if empty
    {loop_rec,{f,17},{x,0}}.
     %% Dummy forward jump
    {move,{atom,false},{x,0}}.
    {test,is_eq,{f,16},[{x,0},{atom,true}]}.
{label,15}.
    {loop_rec,{f,17},{x,0}}.
    {test_heap,3,1}.
    {put_tuple,2,{x,1}}.
    {put,{atom,message}}.
    {put,{x,0}}.
    {move,{x,1},{x,0}}.
    {deallocate,1}.
    return.
{label,16}.
    {loop_rec_end,{f,15}}.
{label,17}.
    {wait_timeout,{f,15},{y,0}}.
    {move,{atom,timeout},{x,0}}.
    {deallocate,1}.
    return.

%%
%% remove() -> true | false
%%
%% Description:
%%    Remove current message. Returns true if a message was
%%    removed, false otherwise
%% 
%%
%% return true | false
{function, remove, 0, 19}.
{label,18}.
    {func_info,{atom,message},{atom,remove},0}.
{label,19}.
    {loop_rec,{f,20},{x,0}}.
    remove_message.
    {move,{atom,true},{x,0}}.
    return.
{label,20}.
    {move,{atom,false},{x,0}}.
    return.

%%
%% Standard module info
%%

{function, module_info, 0, 21}.
{label,21}.
    {func_info,{atom,message},{atom,module_info},0}.
{label,22}.
    {move,{atom,message},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 24}.
{label,23}.
    {func_info,{atom,message},{atom,module_info},1}.
{label,24}.
    {move,{x,0},{x,1}}.
    {move,{atom,message},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
