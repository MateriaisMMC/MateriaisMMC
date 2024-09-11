function [r,B] = raioGSeidel(A)
%raioGSeidel - C�lculo da matriz de itera��o de Gauss-Seidel e do respetivo 
%              raio espetral
%
% [r,B] = raioGSeidel(A)  Calcula a matriz de itera��o de Gauss-Seidel e
%                      respetivo raio espetral para uma dada matriz A
%                     
%------------------------------------------------------------------------
%   INPUT:
%       A -  matriz quadrada (matriz do sistema)
%                        
%   OUTPUT:
%       r - raio espetral da matriz de itera��o de Gauss-Seidel
%
%    Opcional:
%        B -  matriz de itera��o de Gauss-Seidel             
%---------------------------------------------------------------------
%     VERIFICA��ES SOBRE A MATRIZ DE ENTRADA
%---------------------------------------------------------------------
% Verificar se a matriz A � quadrada e n�o tem elementos nulos na diagonal
    [n,m]=size(A); 
    if  ( ~(n==m) )
        error('Matriz nao � quadrada)')
    elseif ~(all(diag(A)))
        error('A tem um elemento nulo na diagonal')
    end
%--------------------------------------------------------------------
% C�lculo da matriz de itera��o de Gauss-Seidel e do respetivo raio
% espetral
B = -tril(A)\triu(A,1); %  Matriz de itera��o de Gauss-Seidel
                         % -inv(D+M)*N
r = max(abs(eig(B)));  %  Raio espetral de B
