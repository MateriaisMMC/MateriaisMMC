function b=subDireta(L,b)
%subDireta resolve sistema triangular inferior (substitui��o direta).
%
% b=subDireta(L,b)   Determina a solu��o de um sistema Lx=b, onde L
%   � uma matriz triangular inferior, por substitui��o direta.
%
% INPUT:
%    L: matriz quadrada, triangular inferior, sem elementos
%       nulos na diagonal (matriz do sistema)
%    b: vetor coluna (termos independentes)
%
% OUTPUT:
%    b: solu��o do sistema Lx=b

%------------------------------------------------------------------------
%             Verifica��o dos par�metros de entrada
%------------------------------------------------------------------------
% Verifica se a matriz L � quadrada, triangular inferior sem elementos
% nulos na diagonal e se b tem a dimens�o adequada.
[n,m]=size(L); [nb,mb]=size(b);
if  ( n~=m )
    error('Matriz n�o � quadrada')
elseif ( nb~=n | mb~=1 )
    error('Vetor b n�o tem a dimens�o adequada')
elseif  ~( all(diag(L)) )
    error('L tem um elemento nulo na diagonal')
elseif ~( isequal(triu(L,1),zeros(n,n)) )
    error('L n�o � triangular inferior')
end
%------------------------------------------------------------------------
%                     Substitui��o direta
%------------------------------------------------------------------------
for i=1:n
    j=1:i-1;
    b(i)=(b(i)-L(i,j)*b(j))/L(i,i);
end