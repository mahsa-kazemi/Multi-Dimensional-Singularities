#################################################
# File:Non_Persistent_Source.mm                 #
#    Authors Contact:                           #
#    Majid Gazor  <mgazor@cc.iut.ac.ir>         #
#    Amir Hashemi <amir.hashemi@cc.iut.ac.ir>   #
#    Mahsa Kazemi <mahsa.kazemi@math.iut.ac.ir> #
#################################################
with(Groebner):
with(PolynomialIdeals):
#with(combinat):
#with(VectorCalculus):
#with(LinearAlgebra):
#<-----------------------------------------------------------------------------
# Function: {Mult_Deriv}
# Description: {}
# Calling sequence:
# {}
# Input:
# {}
# {}
# {}
# Output:
# {}
#>-----------------------------------------------------------------------------
Mult_Deriv := proc(P_in, vars_in)
local out_deriv:
	out_deriv := [seq(diff(P_in, elem), elem in vars_in)];
	return out_deriv;
end proc:
#<-----------------------------------------------------------------------------
# Function: {Bifurcation}
# Description: {derives bifurcation variety for a multi-dim parametric singularity with arbitrary number of variables}
# Calling sequence:
# {Bifurcation(G_in, vars_in, params_in)}
# Input:
# {G_in : a multi-dim parametric singularity }
# {vars_in : a list of variables}
# {params_in : a list of parameters}
# Output:
# { a semi-algebraic set in terms of parameters}
#>-----------------------------------------------------------------------------
Bifurcation:= proc(G_in::list, vars_in::list, params_in::list)
local out_list_deriv, out_mult_newvars, out_ready, i, j, k, J, final_output :

	out_list_deriv := map(Mult_Deriv, G_in, vars_in);
	out_mult_newvars := [seq([seq(v[i]*elem, elem = out_list_deriv[i])], i = 1 .. nops(out_list_deriv))];
	out_ready := seq(add(k, k = [seq(out_mult_newvars[i][j], i = 1 .. nops(out_mult_newvars))]), j = 1 .. nops(vars_in));
	J := <out_ready,op(G_in),-zeta*(sum(v[i]^2, i = 1 ..nops(out_list_deriv)))+1>;
	final_output := EliminationIdeal(J, {op(params_in)});
	return final_output;
end proc:
#<-----------------------------------------------------------------------------
# Function: {First_Deriv}
# Description: {}
# Calling sequence:
# {Bifurcation(P_in, vars_in, params_in)}
# Input:
# {P_in :  }
# {vars_in : a list of variables}
# {params_in : a list of parameters}
# Output:
# {}
#>-----------------------------------------------------------------------------
First_Deriv := proc(P_in, vars_in, v)
local  A, B:
	A := [seq(diff(P_in, vars_in[i])*v[i], i=1..nops(vars_in))];
	B := add(j, j=A);
	return B;
end proc:

Second_Deriv := proc(P_in, vars_in, v)
local A, i, A_out, j, B_bef, C_bef, B, B_out, k, second_out, jj:
	A := [seq(diff(P_in, [vars_in[i]$2])*v[i]^2, i=1..nops(vars_in))];
	A_out := add(j, j=A);
	B_bef := combinat:-choose(vars_in, 2); 
	C_bef := combinat:-choose(v, 2);
	B := [seq(2*diff(P_in, op(B_bef[jj]))*C_bef[jj][1]*C_bef[jj][2], jj=1..nops(C_bef))];
	B_out := add(k, k=B);
	second_out := A_out+B_out;
	return second_out;
end proc:
#<-----------------------------------------------------------------------------
# Function: {Hysteresis}
# Description: {derives hysteresis variety for a multi-dim parametric singularity with arbitrary number of variables}
# Calling sequence:
# {Hysteresis(G_in, vars_in, params_in)}
# Input:
# {G_in : a multi-dim parametric singularity }
# {vars_in : a list of variables}
# {params_in : a list of parameters}
# Output:
# { a semi-algebraic set in terms of parameters}
#>-----------------------------------------------------------------------------
Hysteresis := proc(G_in::list, vars_in::list, params_in::list)
local First_output,w, v, i, j, Intermediate_output, Second_output, second_final, J, final_output :
	v := [seq(v[i], i=1..nops(vars_in))];
	w := [seq(w[j], j=1..nops(vars_in))];
	First_output := map(First_Deriv, G_in, vars_in, v);
	Intermediate_output := map(First_Deriv, G_in, vars_in, w);
	Second_output := map(Second_Deriv, G_in, vars_in, v);
	second_final := Second_output-Intermediate_output;
	J := <op(G_in), op(First_output), op(second_final), -zeta*(sum(v[i]^2, i = 1 ..nops(v)))+1>;
	final_output :=EliminationIdeal(J, {op(params_in)});
	return final_output;
end proc:
#<-----------------------------------------------------------------------------
# Function: {DoubleLimitPoint}
# Description: {derives double limit point variety for a multi-dim parametric singularity with arbitrary number of variables}
# Calling sequence:
# {DoubleLimitPoint(G_in, vars_in, params_in)}
# Input:
# {G_in : a multi-dim parametric singularity }
# {vars_in : a list of variables}
# {params_in : a list of parameters}
# Output:
# { a semi-algebraic set in terms of parameters}
#>-----------------------------------------------------------------------------
DoubleLimitPoint := proc(G_in::list, vars_in::list, params_in::list)
local G_first, i, j, G_second, Jacob_out, det_out, det_first, det_second, J, final_output:
	G_first := subs([seq(vars_in[i]=x[i], i=1..nops(vars_in))], G_in);
	G_second := subs([seq(vars_in[j]=y[j], j=1..nops(vars_in))], G_in);
	Jacob_out := VectorCalculus:-Jacobian(G_in, vars_in);
	det_out := LinearAlgebra:-Determinant(Jacob_out);
	det_first := subs([seq(vars_in[i]=x[i], i=1..nops(vars_in))], det_out);
	det_second := subs([seq(vars_in[i]=y[i], i=1..nops(vars_in))], det_out);
	J :=  op(G_first), op(G_second), det_first, det_second, -zeta*(sum((x[k]-y[k])^2, k = 1 ..nops(vars_in)))+1;
	#J:=[op(G_first), op(G_second), det_first, det_second, -zeta*(sum((x[k]-y[k])^2, k = 1 ..nops(vars_in)))+1];
	final_output :=EliminationIdeal(<J>, {op(params_in)});
	return final_output;
end proc:
