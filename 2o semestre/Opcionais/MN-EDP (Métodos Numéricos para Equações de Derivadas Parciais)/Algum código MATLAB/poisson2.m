function U=poisson2(f,a,b,m,f0,f1,g0,g1)
% poisson2.m  -- resolve o problema de Poisson
%                u_{xx} + u_{yy} = f(x,y)
% em [a,b] x [a,b], com condições de Dirichlet
%                 u(x,a)=f0(x) e u(x,b)=f1(x)
%                 u(a,y)=g0(y) e u(b,y)=g1(x)
% 
% usando a fórmula dos 5 pontos.
% m=M-1 (notação slides)
% 
% Esta função foi adaptada de
% http://faculty.washington.edu/rjl/fdmbook/matlab/poisson.m
h = (b-a)/(m+1);
x = linspace(a,b,m+2);   % pontos malha x incluindo a fronteira
y = linspace(a,b,m+2);   % pontos malha y incluindo a fronteira
U=zeros(m+2,m+2);

[X,Y] = meshgrid(x,y);      %
X = X';                     % transposta de modo que X(i,j),Y(i,j) são
Y = Y';                     % coordenadas (i,j) pontos

Iint = 2:m+1;              % índices dos pontos interiores em x
Jint = 2:m+1;              % índices dos pontos interiores em y
Xint = X(Iint,Jint);       % pontos interiores
Yint = Y(Iint,Jint);

b = h^2*f(Xint,Yint);   % avaliação de f nos pontos interiores para 
                         % formar vetor b (vão ser alterados pelas 
                         % condições de fronteira).

% definir as condições de fronteira:

U(:,1) = f0(x); % y=a
U(:,m+2) = f1(x); % y=b
U(1,:) = g0(y); % x=a
U(m+2,:) = g1(y); % x=b

% ajustar b para incluir condições de fronteira:

b(:,1) = b(:,1) - U(Iint,1);
b(:,m) = b(:,m) - U(Iint,m+2);
b(1,:) = b(1,:) - U(1,Jint);
b(m,:) = b(m,:) - U(m+2,Jint);


% converter b num vetor coluna:
B = reshape(b,m*m,1);


% formar a matriz A:
I = speye(m);
e = ones(m,1);
% usar produto de kronecker (ver Exercício 3.15)
T = spdiags([e -2*e e],[-1 0 1],m,m);
A = kron(I,T) + kron(T,I);

% Resolver o sistema
uvec = A\B;

% fazer o reshape do vetor solução de forma a ter uma grelha com os valores
% da solução

U(Iint,Jint) = reshape(uvec,m,m);
end

