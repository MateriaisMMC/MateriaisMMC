function valp=polLagrange(x,y,z)

% POLLAGRANGE  polinómio interpolador na forma de Lagrange
%
% VALP=POLLAGRANGE(X,Y,Z)   calcula P(Z), onde P é o polinómio
%    interpolador dos pontos (X,Y). 
%    O polinómio P (de grau <= n-1, onde n=length(X)) é obtido 
%    usando a forma de Lagrange.
%
%    PARÂMETROS DE ENTRADA:
%
%    X=(x1,...,xn) vector real de componentes distintas (abcissas);
%    Y=(y1,...,yn) vector real com a mesma dimensão que X;
%    Z=(z1,...,zm) vector real dos pontos onde se pretende calcular 
%                  o valor do polinómio interpolador.
%                        
%    PARÂMETRO DE SAÍDA:
%
%    VALP=(P(z1),...,P(zm)), onde P é o polinómio de grau <=n-1 
%    interpolador dos pontos (xi,yi). 
%    Cada valor P(zi) é calculado usando a forma de Lagrange: 
%                 P(zi)=L1(zi) y1+...+Ln(zi) yn , 
%    onde Lk(z) sao os polinómios de Lagrange relativos aos pontos xi.
%   

n=length(x);
%------------------------------------------------------------------------
%             VERIFICAÇÕES SOBRE PARÂMETROS DE ENTRADA
%------------------------------------------------------------------------
% Verificar se x e y sao da mesma dimensão
if length(y) ~= n 
 error('Os vectores x e y devem ser da mesma dimensão.');
end
% Verificar se os elementos de x são distintos
h=diff(x); % Usa a funcao pré-definida diff.
if any(h == 0)
   error('As abcissas devem ser distintas.')
end
% Verificar se x e y sao vectores reais
if ~isreal(x)
   error('As abcissas devem ser reais.')
end
if ~isreal(y)
    error('As ordenadas devem ser reais.')
end
m=length(z);
% Criação  da matriz m*n dos coeficientes Lk
% (Formamos uma matriz que tem, na linha i, os valores dos diversos
% polinómios de Lagrange L1,..., Ln no ponto zi)
L=zeros(m,n);
for i=1:m
    for k=1:n
        xmenxk=x;
        xmenxk(k)=[]; % formar o vector (x1,...,xk-1,xk+1,...,xn)
        L(i,k)=prod((z(i)-xmenxk)./(x(k)-xmenxk));
    end
end
%  Caso y seja um vector linha, transformá-lo num vector coluna, para
%  poder pré-multiplicar y por L
if size(y,1)==1, y=y'; end
%  Cálculo de valpz 
%  (Transpomos o resultado por comodidade, para que valplz saia como 
%  um vector linha)
valp=(L*y); 
               