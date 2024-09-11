function [r,B]=raioJacobi(A)
% raioJacobi -  Cálculo da matriz de iteração de Jacobi e do respetivo 
%              raio espetral
%
% [r,B] = raioJacobi(A)  Calcula a matriz de iteração de Jacobi e 
%                     respetivo raio espetral para uma dada matriz A
%                     
%------------------------------------------------------------------------
%   INPUT:
%       A -  matriz quadrada (matriz do sistema)
%                        
%   OUTPUT:
%       r - raio espetral da matriz de iteração de Jacobi
%
%    Opcional:
%        B -  matriz de iteração de Jacobi               
%---------------------------------------------------------------------
%     VERIFICAÇÕES SOBRE A MATRIZ DE ENTRADA
%---------------------------------------------------------------------
% Verificar se a matriz A é quadrada e não tem elementos nulos na diagonal
    [n,m]=size(A); 
    if  ( ~(n==m) )
        error('Matriz não é quadrada)')
    elseif ~(all(diag(A)))
        error('A tem um elemento nulo na diagonal')
    end
%--------------------------------------------------------------------
% Cálculo da matriz de iteração de Jacobi e do respetivo raio espetral
dA = diag(A);
B = diag(dA)-A; % Matriz -(M+N)
B = B./dA;      % Matriz -inv(D)*(M+N)
r = max(abs(eig(B))); % Raio espetral da matriz B
