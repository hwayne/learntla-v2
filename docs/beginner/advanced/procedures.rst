.. index:: 
  single: procedure
  single: call
  single: return
  seealso: return; procedure
  seealso: call; procedure

.. _procedure:

Procedures
-----------

*Note: this is both fairly complicated and fairly niche, so feel free to skip this and come back to it later.*

If you want two separate processes to share some spec, you can extract the common bit into a macro. But what if you want to extract something more complicated, with labels? For this, instead of macros we use **procedures**. They're like macros, except they can contain labels, and they're a little more complicated to write and use. 

To use procedures, you must extend ``Sequences``. This is because the translator needs to store a call stack for control flow, which is does in a tuple. 

::

  procedure Name(arg1, ...)
  variables var1 = ... 
  begin
    Label1:
      \* stuff
    Label2:
      \* more stuff
      return;
  end procedure;

.. index:: return
  :name: return

On reaching a ``return``, the procedure terminates and returns control back to the calling process. Nothing is "returned" as per the programming definition. If a procedure terminates without reaching a ``return``, then TLC will raise an error. the The return just ends the procedure. If your procedure never reaches it, then it's an error.

In order to call a procedure, you have to write ``call Name(val1, ...);``. A procedure call must be followed by a `goto`, a label, or another ``return`` (if you called it from another procedure).

Procedures must be defined after any macros and before any processes.


.. todo::

  * An example


