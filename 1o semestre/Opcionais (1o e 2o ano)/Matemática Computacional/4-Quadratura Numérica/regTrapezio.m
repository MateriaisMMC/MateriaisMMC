function [int_Aprox,est_erro]=regTrapezio(f,a,b,N)

% regTrapezio Calcula uma aproximação para um integral definido usando  
%              a regra do trapézio (composta) com N subintervalos
%              e, se N for par, calcula uma estimativa para o respetivo erro.
%
% [int_Aprox,est_erro] = regTrapezio(f,a,b,N)
%   Calcula uma aproximação para o valor do integral entre a e b da
%   função f, usando a regra do trapézio com N subintervalos
%   e, se N for par, determina uma estimativa para o erro dessa aproximação.
%
%   INPUT:
%     f: função integranda;
%     a,b: reais (com a<b) correspondentes aos extremos do intervalo de
%          integração;
%   Opcional:
%      N: número de subintervalos
%         Por defeito, é usado N = 1 (regra do trapézio simples)
%
%   OUTPUT:
%     int_Aprox: aproximação para o integral calculada usando a regra do
%               trapézio com N subintervalos;
%    
%    Opcional:
%    est_erro: estimativa para o erro, obtida calculando um novo valor para
%           o integral, int_Aprox2, com N/2 subintervalos, e usando a fórmula
%           est_erro=|int_Aprox-int_Aprox2|/3.
%
%------------------------------------------------------------------------
%             VERIFICAÇÃO DOS PARÂMETROS DE ENTRADA
%------------------------------------------------------------------------
if nargin < 4
    N = 1; %Regra do trapézio simples
end
if nargin < 3
    error('Tem de introduzir a função f e os extremos do intervalo')
end
% Verificar se a<b e se N é inteiro
if  a>=b
    error('a deve ser menor que b')
end
if ~(mod(N,1) == 0&&N>0)
     error('N deve ser inteiro positivo')
end

% Determinação de h e construção do vetor das abcissas
h = (b-a)/N;
abcissas = a:h:b;

% Regra do trapézio om N subintervalos
y = f(abcissas);
int_Aprox = (h/2)*(y(1)+2*sum(y(2:end-1))+y(end));

if nargout == 2
    if mod(N,2)~=0 
        disp('Para estimar o erro, N tem de ser par')
        est_erro =[];
    else 
        % Cálculo da aproximação para o integral usando metade dos subintervalos
        int_Aprox2 = h*(y(1)+2*sum(y(3:2:end-2))+y(end));

        %  Cálculo da estimativa para o erro
        est_erro=abs(int_Aprox-int_Aprox2)/3;
    end
end