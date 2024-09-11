function [x,est]=metGSeidel(A,b,tol,maxit,x0,impr)
%metGSeidel Resolução de um sistema linear pelo método iterativo de 
%           Gauss-Seidel
%
% [x,est] = metGSeidel(A,b,tol,maxit,x0,impr)   
%   Determinação da solução aproximada do sistema Ax=b e de uma 
%   estimativa para o respetivo erro, usando o método iterativo de Gauss-Seidel.
%
%   O processo iterativo é interrompido quando a norma infinita
%   da diferença das duas últimas iteradas calculadas for inferior 
%   ao valor de uma certa tolerância, tol, ou quando for
%   atingido um número máximo de iterações permitidas, maxit. 
%
%   O processo é inicializado com o vetor x0 e, se impr=1, os resultados 
%   intermédios são visualizados.
%---------------------------------------------------------------------
% 
% INPUT:
%       A: matriz quadrada (matriz do sistema)
%       b: vetor coluna (lado direito do sistema)
%
%   Opcionais:
%       tol: real positivo (tolerância para a estimativa do erro)
%            Por defeito, tol = 0.5e-6
%       maxit: inteiro positivo (número máximo de iterações permitidas) 
%            Por defeito, maxit = 30
%       x0: vetor coluna, com o mesmo número de elementos de b 
%           (vetor aproximação inicial) 
%            Por defeito, x0 é o vetor nulo
%       impr: usar impr = 1, se pretendermos visualizar os resultados 
%             intermédios
%            Por defeito, impr = 0
%          
% OUTPUT:
%       x: solução aproximada do sistema  
%
%   Opcional:
%      est: estimativa para o erro na solução 
%          (norma infinita da diferença das 2 últimas iteradas)     
%

%---------------------------------------------------------------------
%      Verificações sobre as entradas
%---------------------------------------------------------------------
% Verificar se existe o número mínimo de entradas
if (nargin <2 )
   error('Tem de introduzir a matriz A e o vetor b');
end
% Verificar se a matriz A é quadrada, se b tem a dimensão adequada e se
% A não tem elementos nulos na diagonal
[n,m] = size(A); [nb,mb] = size(b);
if  ( n ~= m ) 
	error('A matriz do sistema não é quadrada)')
end
if ( nb ~= m || mb ~= 1 )
	error('O vetor do lado direito do sistema não tem a dimensão adequada')
end
if ~(all(diag(A)))
	 error('A matriz do sistema tem um elemento nulo na diagonal')
end
%--------------------------------------------------------------------------
%       Valores de argumentos por defeito
%--------------------------------------------------------------------------
if ( nargin < 6 ), impr = 0; end 
if ( nargin < 5 || isempty(x0) ), x0 = zeros(n,1); end
if ( nargin < 4 || isempty(maxit) ), maxit = 30; end
if ( nargin < 3 || isempty(tol) ), tol = 0.5e-6; end

%------------------------------------------------------------------------
%                         PROCESSO ITERATIVO
%------------------------------------------------------------------------
DmaisM = tril(A); % Matriz D+M
N = triu(A,1);	%   Matriz N                      
niter = 0;      % Inicialização do contador do número de iterações
while  niter < maxit 
    x = subDireta(DmaisM,-N*x0+b); % Cálculo da nova iterada
    est = norm(x-x0,inf);         % Cálculo da estimativa para o erro
    niter = niter+1;	          % Incremento do número de iterações
    if impr == 1  % Visualização de resultados intermédios                                
        fprintf('\n k = %3.0f \n',niter)
        disp('Vetor aproximação')
        fprintf('%12.8f \n',x)
        disp('Estimativa para o erro')
        fprintf('%4.2e \n',est)
    end
 % --------------------------------------------------------------------
    if est < tol
       disp(' ')
       disp(['O Método de Gauss Seidel atingiu a precisão desejada em ',num2str(niter), ' iterações'])
       disp(' ')
       break
    end
    x0 = x; % Armazenamento em x0 da última iterada calculada
end
%------------------------------------------------------------------------
%    Mensagem caso se tenha atingido o limite de iterações
%------------------------------------------------------------------------
if (niter == maxit && (est >= tol||isnan(est)))
   disp(' ')
   disp(['Ao fim de ',num2str(maxit), '  iterações do Método de Gauss Seidel, não se atingiu a precisão desejada'])
end