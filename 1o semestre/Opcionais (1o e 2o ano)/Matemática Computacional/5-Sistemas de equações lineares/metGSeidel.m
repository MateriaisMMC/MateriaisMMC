function [x,est]=metGSeidel(A,b,tol,maxit,x0,impr)
%metGSeidel Resolu��o de um sistema linear pelo m�todo iterativo de 
%           Gauss-Seidel
%
% [x,est] = metGSeidel(A,b,tol,maxit,x0,impr)   
%   Determina��o da solu��o aproximada do sistema Ax=b e de uma 
%   estimativa para o respetivo erro, usando o m�todo iterativo de Gauss-Seidel.
%
%   O processo iterativo � interrompido quando a norma infinita
%   da diferen�a das duas �ltimas iteradas calculadas for inferior 
%   ao valor de uma certa toler�ncia, tol, ou quando for
%   atingido um n�mero m�ximo de itera��es permitidas, maxit. 
%
%   O processo � inicializado com o vetor x0 e, se impr=1, os resultados 
%   interm�dios s�o visualizados.
%---------------------------------------------------------------------
% 
% INPUT:
%       A: matriz quadrada (matriz do sistema)
%       b: vetor coluna (lado direito do sistema)
%
%   Opcionais:
%       tol: real positivo (toler�ncia para a estimativa do erro)
%            Por defeito, tol = 0.5e-6
%       maxit: inteiro positivo (n�mero m�ximo de itera��es permitidas) 
%            Por defeito, maxit = 30
%       x0: vetor coluna, com o mesmo n�mero de elementos de b 
%           (vetor aproxima��o inicial) 
%            Por defeito, x0 � o vetor nulo
%       impr: usar impr = 1, se pretendermos visualizar os resultados 
%             interm�dios
%            Por defeito, impr = 0
%          
% OUTPUT:
%       x: solu��o aproximada do sistema  
%
%   Opcional:
%      est: estimativa para o erro na solu��o 
%          (norma infinita da diferen�a das 2 �ltimas iteradas)     
%

%---------------------------------------------------------------------
%      Verifica��es sobre as entradas
%---------------------------------------------------------------------
% Verificar se existe o n�mero m�nimo de entradas
if (nargin <2 )
   error('Tem de introduzir a matriz A e o vetor b');
end
% Verificar se a matriz A � quadrada, se b tem a dimens�o adequada e se
% A n�o tem elementos nulos na diagonal
[n,m] = size(A); [nb,mb] = size(b);
if  ( n ~= m ) 
	error('A matriz do sistema n�o � quadrada)')
end
if ( nb ~= m || mb ~= 1 )
	error('O vetor do lado direito do sistema n�o tem a dimens�o adequada')
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
niter = 0;      % Inicializa��o do contador do n�mero de itera��es
while  niter < maxit 
    x = subDireta(DmaisM,-N*x0+b); % C�lculo da nova iterada
    est = norm(x-x0,inf);         % C�lculo da estimativa para o erro
    niter = niter+1;	          % Incremento do n�mero de itera��es
    if impr == 1  % Visualiza��o de resultados interm�dios                                
        fprintf('\n k = %3.0f \n',niter)
        disp('Vetor aproxima��o')
        fprintf('%12.8f \n',x)
        disp('Estimativa para o erro')
        fprintf('%4.2e \n',est)
    end
 % --------------------------------------------------------------------
    if est < tol
       disp(' ')
       disp(['O M�todo de Gauss Seidel atingiu a precis�o desejada em ',num2str(niter), ' itera��es'])
       disp(' ')
       break
    end
    x0 = x; % Armazenamento em x0 da �ltima iterada calculada
end
%------------------------------------------------------------------------
%    Mensagem caso se tenha atingido o limite de itera��es
%------------------------------------------------------------------------
if (niter == maxit && (est >= tol||isnan(est)))
   disp(' ')
   disp(['Ao fim de ',num2str(maxit), '  itera��es do M�todo de Gauss Seidel, n�o se atingiu a precis�o desejada'])
end