function b=subinversa(U,b)
% subinversa resolve sistema triangular superior (por substitui��o inversa).
%
% b=subinversa(U,b)   Determina a solu��o de um sistema Ux=b, onde U
%   � uma matriz triangular superior, por substitui��o inversa.
%
% INPUT:
%    U: matriz quadrada, triangular superior, sem elementos diagonais nulos
%    b: vetor coluna (termos independentes)
%                        
% OUTPUT:
%    b: vetor solu��o do sistema Ux=b

%------------------------------------------------------------------------
%             Verifica��o dos par�metros de entrada
%------------------------------------------------------------------------
% Verifica se a matriz U � quadrada, triangular superior sem elementos 
% nulos na diagonal e se b tem a  dimens�o adequada.
[n,m]=size(U); [nb,mb]=size(b);
if  ( ~(n==m) )
    error('Matriz n�o � quadrada)')
elseif ( ~(nb==n) | ~(mb==1) )
    error('Vetor b n�o tem a dimens�o adequada')
elseif( all(diag(U))==0 )
    error('U tem um elemento nulo na diagonal')
elseif ~(isequal(tril(U,-1),zeros(n,n)))
    error('U n�o � triangular superior')
end
%------------------------------------------------------------------------
%                     Substitui��o inversa
%------------------------------------------------------------------------
for i=n:-1:1
    j=i+1:n;
    b(i)=(b(i)-((U(i,j)*b(j))))/U(i,i);
end



 
            
            
            