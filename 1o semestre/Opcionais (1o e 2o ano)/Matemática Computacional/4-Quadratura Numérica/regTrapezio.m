function [int_Aprox,est_erro]=regTrapezio(f,a,b,N)

% regTrapezio Calcula uma aproxima��o para um integral definido usando  
%              a regra do trap�zio (composta) com N subintervalos
%              e, se N for par, calcula uma estimativa para o respetivo erro.
%
% [int_Aprox,est_erro] = regTrapezio(f,a,b,N)
%   Calcula uma aproxima��o para o valor do integral entre a e b da
%   fun��o f, usando a regra do trap�zio com N subintervalos
%   e, se N for par, determina uma estimativa para o erro dessa aproxima��o.
%
%   INPUT:
%     f: fun��o integranda;
%     a,b: reais (com a<b) correspondentes aos extremos do intervalo de
%          integra��o;
%   Opcional:
%      N: n�mero de subintervalos
%         Por defeito, � usado N = 1 (regra do trap�zio simples)
%
%   OUTPUT:
%     int_Aprox: aproxima��o para o integral calculada usando a regra do
%               trap�zio com N subintervalos;
%    
%    Opcional:
%    est_erro: estimativa para o erro, obtida calculando um novo valor para
%           o integral, int_Aprox2, com N/2 subintervalos, e usando a f�rmula
%           est_erro=|int_Aprox-int_Aprox2|/3.
%
%------------------------------------------------------------------------
%             VERIFICA��O DOS PAR�METROS DE ENTRADA
%------------------------------------------------------------------------
if nargin < 4
    N = 1; %Regra do trap�zio simples
end
if nargin < 3
    error('Tem de introduzir a fun��o f e os extremos do intervalo')
end
% Verificar se a<b e se N � inteiro
if  a>=b
    error('a deve ser menor que b')
end
if ~(mod(N,1) == 0&&N>0)
     error('N deve ser inteiro positivo')
end

% Determina��o de h e constru��o do vetor das abcissas
h = (b-a)/N;
abcissas = a:h:b;

% Regra do trap�zio om N subintervalos
y = f(abcissas);
int_Aprox = (h/2)*(y(1)+2*sum(y(2:end-1))+y(end));

if nargout == 2
    if mod(N,2)~=0 
        disp('Para estimar o erro, N tem de ser par')
        est_erro =[];
    else 
        % C�lculo da aproxima��o para o integral usando metade dos subintervalos
        int_Aprox2 = h*(y(1)+2*sum(y(3:2:end-2))+y(end));

        %  C�lculo da estimativa para o erro
        est_erro=abs(int_Aprox-int_Aprox2)/3;
    end
end