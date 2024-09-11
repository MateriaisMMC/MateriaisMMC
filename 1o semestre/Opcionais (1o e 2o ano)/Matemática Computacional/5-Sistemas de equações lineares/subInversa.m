function b=subinversa(U,b)
% subinversa resolve sistema triangular superior (por substituição inversa).
%
% b=subinversa(U,b)   Determina a solução de um sistema Ux=b, onde U
%   é uma matriz triangular superior, por substituição inversa.
%
% INPUT:
%    U: matriz quadrada, triangular superior, sem elementos diagonais nulos
%    b: vetor coluna (termos independentes)
%                        
% OUTPUT:
%    b: vetor solução do sistema Ux=b

%------------------------------------------------------------------------
%             Verificação dos parâmetros de entrada
%------------------------------------------------------------------------
% Verifica se a matriz U é quadrada, triangular superior sem elementos 
% nulos na diagonal e se b tem a  dimensão adequada.
[n,m]=size(U); [nb,mb]=size(b);
if  ( ~(n==m) )
    error('Matriz não é quadrada)')
elseif ( ~(nb==n) | ~(mb==1) )
    error('Vetor b não tem a dimensão adequada')
elseif( all(diag(U))==0 )
    error('U tem um elemento nulo na diagonal')
elseif ~(isequal(tril(U,-1),zeros(n,n)))
    error('U não é triangular superior')
end
%------------------------------------------------------------------------
%                     Substituição inversa
%------------------------------------------------------------------------
for i=n:-1:1
    j=i+1:n;
    b(i)=(b(i)-((U(i,j)*b(j))))/U(i,i);
end



 
            
            
            