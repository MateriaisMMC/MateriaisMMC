function [u,xx,tt] = adveccaoLW(f,h,k,T,a)
% adveccaoLW resolve a equação de advecção 1D, usando o método
% Lax Wendroff
%    u = adveccaoLW(f,a,h,k,T) resolve o problema modelo 
%                 u_t+a u_x=0
%                 u(x,0)=f(x), 0<x<1 (condições iniciais)
%                 u(0,t)=0, t>0 (condições de fronteira)
%               
%
%           * f é a 'function handle' que define a condição inicial
%           * h passo na variável espacial
%           * k passo na variável temporal
%           * T é o instante final
%           * u é a aproximação para a solução do problema nos nós da malha 
%               (i*h,j*k); i=0,...,m; j=0,...,n
%
%    [u,xx,tt] = adveccaoLW(f,h,k,T,a) produz como output
%    adicional as matrizes xx e tt que definem os nós da malha

% Valor dos argumentos por defeito
if nargin <5  
    a = 1; 
end

m=fix(1/h);n=fix(T/k);C=a*k/h;
if C>1
    warning('o método pode sofrer de instabilidade; C= %s',num2str(C))
end

% definição da malha
% é necessário resolver o problema no intervalo [0,1+nh]
m2=m+n;
XX=0:h:1+n*h;
TT=0:k:T;
[xx,tt]=meshgrid(XX,TT);

% construção da matriz tridiagonal 
e=ones(m2-1,1);
A=spdiags([((C^2+C)/2)*e (1-C^2)*e ((C^2-C)/2)*e],[-1 0 1],m2-1,m2-1);

% inicialização da solução; condição inicial
u=zeros(n+1,m2+1);
u(1,:)=f(XX);

% Método explícito
for j=1:n
    b=u(j,2:m2)';
    u(j+1,2:m2)=A*b;
end

u=u(:,1:m+1);
xx=xx(:,1:m+1);
tt=tt(:,1:m+1);
end
