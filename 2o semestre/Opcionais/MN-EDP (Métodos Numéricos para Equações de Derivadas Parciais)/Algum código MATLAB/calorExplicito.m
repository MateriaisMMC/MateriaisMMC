function [u,xx,tt] = calorExplicito(f,m,n,T,L,sigma)
% calorExplicito resolve a equação do calor 1D, usando o método explícito
%    u = calorExplicito(f,m,n,T,L,sigma) resolve o problema modelo 
%                 u_t=sigma u_xx
%                 u(x,0)=f(x), 0<x<L (condições iniciais)
%                 u(0,t)=u(L,t)=0, t>=0 (condições de fronteira)
%
%           * f é a 'function handle' que define a distribuição inicial da
%               temperatura
%           * m é o números de intervalos na variável espacial
%           * n é o número de intervalos na variável temporal
%           * T é o instante final
%           * L é o comprimento do filamento (por defeito é 1)
%           * sigma é o coeficiente de difusão (por defeito é 1)
%           * u é a aproximação para a solução do problema nos nós da malha 
%               (i*L/m,j*T/n); i=0,...,m; j=0,...,n
%
%    [u,xx,tt] = calorExplicito(f,m,n,T,L,sigma) produz como output
%    adicional as matrizes xx e tt que definem os nós da malha


%  Versão: março 2023
%  Autores: M. Irene Falcão e Fernando Miranda

% Valor dos argumentos por defeito
if nargin <6  
    sigma = 1; 
end
if nargin <5 || isempty(L) 
    L = 1; 
end
 
h=L/m;k=T/n;r=sigma*k/h^2;
if r>1/2
    warning('o método pode sofrer de instabilidade; r= %s',num2str(r))
end

% definição da malha
XX=0:h:L;
TT=0:k:T;
[xx,tt]=meshgrid(XX,TT);

% construção da matriz tridiagonal 
e=ones(m-1,1);
A=spdiags([r*e (1-2*r)*e r*e],[-1 0 1],m-1,m-1);

% inicialização da solução e condição inicial
u=zeros(n+1,m+1);
u(1,:)=f(XX);

% Método explícito
for j=1:n
    b=u(j,2:m)';
    u(j+1,2:m)=A*b;
end
end
