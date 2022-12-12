# iterative_convergence
Formalization of the iterative convergence error

We formally prove the following in Coq:
- Necessary and sufficient conditions for convergence of an iterative method. The formalization can be found in the files `iter_necessity.v` and `iter_convergence.v`
- Reich theorem for convergence of a Gauss Seidel iterative method. The formalization can be found in the file `gauss_seidel.v`
- Theorem for convergence of Jacobi iterative method. We instantiate it with a 2nd order difference scheme and prove its convergence. The formalization can be found in the file `jacobi.v`
- generic properties for handling complex matrices and vectors. We define modulus of a complex numbers, generic properties about conjugates of complex numbers. We define complex conjuagates of vector and matrices and lemmas to handle scaling, transpose operations. The formalization can be found in the file `complex_mat_vec_prop.v`.
- some compatibility relations for induced vector and matrix norms can be found in the file `matrix_norm.v`

# Dependencies:

All the developments have been done in Coq 8.12.0. To successfully compile the code, following dependencies are required:
- `mathcomp 1.12.0 or later`
- `mathcomp-analysis 0.5.0 or later`
- `coquelicot 3.2.0`
- `coqeal 1.0.5 or later`
-  `mathcomp real-closed 1.1.2 or later`

# Building and installing instructions

To build and install do:
```
git clone https://github.com/mohittkr/iterative_convergence.git
cd iterative_convergence
make
make install
```
All the files are installed in the `user-contrib/iterative_convergence` folder

