function b=subDireta(L,b)
%subDireta resolve sistema triangular inferior (substituição direta).
%
% b=subDireta(L,b)   Determina a solução de um sistema Lx=b, onde L
%   é uma matriz triangular inferior, por substituição direta.
%
% INPUT:
%    L: matriz quadrada, triangular inferior, sem elementos
%       nulos na diagonal (matriz do sistema)
%    b: vetor coluna (termos independentes)
%
% OUTPUT:
%    b: solução do sistema Lx=b

%------------------------------------------------------------------------
%             Verificação dos parâmetros de entrada
%------------------------------------------------------------------------
% Verifica se a matriz L é quadrada, triangular inferior sem elementos
% nulos na diagonal e se b tem a dimensão adequada.
[n,m]=size(L); [nb,mb]=size(b);
if  ( n~=m )
    error('Matriz não é quadrada')
elseif ( nb~=n | mb~=1 )
    error('Vetor b não tem a dimensão adequada')
elseif  ~( all(diag(L)) )
    error('L tem um elemento nulo na diagonal')
elseif ~( isequal(triu(L,1),zeros(n,n)) )
    error('L não é triangular inferior')
end
%------------------------------------------------------------------------
%                     Substituição direta
%------------------------------------------------------------------------
for i=1:n
    j=1:i-1;
    b(i)=(b(i)-L(i,j)*b(j))/L(i,i);
end