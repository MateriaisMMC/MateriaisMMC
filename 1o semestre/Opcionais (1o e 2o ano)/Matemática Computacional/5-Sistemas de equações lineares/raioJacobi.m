function [r,B]=raioJacobi(A)
% raioJacobi -  C�lculo da matriz de itera��o de Jacobi e do respetivo 
%              raio espetral
%
% [r,B] = raioJacobi(A)  Calcula a matriz de itera��o de Jacobi e 
%                     respetivo raio espetral para uma dada matriz A
%                     
%------------------------------------------------------------------------
%   INPUT:
%       A -  matriz quadrada (matriz do sistema)
%                        
%   OUTPUT:
%       r - raio espetral da matriz de itera��o de Jacobi
%
%    Opcional:
%        B -  matriz de itera��o de Jacobi               
%---------------------------------------------------------------------
%     VERIFICA��ES SOBRE A MATRIZ DE ENTRADA
%---------------------------------------------------------------------
% Verificar se a matriz A � quadrada e n�o tem elementos nulos na diagonal
    [n,m]=size(A); 
    if  ( ~(n==m) )
        error('Matriz n�o � quadrada)')
    elseif ~(all(diag(A)))
        error('A tem um elemento nulo na diagonal')
    end
%--------------------------------------------------------------------
% C�lculo da matriz de itera��o de Jacobi e do respetivo raio espetral
dA = diag(A);
B = diag(dA)-A; % Matriz -(M+N)
B = B./dA;      % Matriz -inv(D)*(M+N)
r = max(abs(eig(B))); % Raio espetral da matriz B
