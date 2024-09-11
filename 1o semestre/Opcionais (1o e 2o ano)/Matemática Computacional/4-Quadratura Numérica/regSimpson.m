function [int_Aprox,est_erro] = regSimpson(f,a,b,N)

% regSimpson Calcula uma aproximação para um integral definido usando a 
%             regra de Simpson (composta) e, se N for múltiplo de 4,
%             calcula uma estimativa para o respetivo erro.
%
% [int_Aprox,est_erro] = regSimpson(f,a,b,N)
%   Calcula uma aproximação para o valor do integral entre a e b da
%   função f, usando a regra de Simpson composta com N subintervalos
%   e, se N for múltiplo de 4, determina uma estimativa para o erro dessa
%   aproximação.
%
%   ENTRADAS:
%     f: função integranda;
%     a,b: reais (com a<b) correspondentes aos extremos do intervalo de 
%          integração;
%   Opcional:
%      N: número de subintervalos
%         Por defeito, é usado N = 2 (regra de Simpson simples)
%                         
%   SAÍDAS:
%     int_Aprox: aproximação para o integral calculada usando a regra de
%               Simpson composta com N subintervalos;
%   Opcional:
%     est_erro: estimativa para o erro, obtida calculando um novo valor para
%           o integral, int_Aprox2, com N/2 subintervalos e usando a
%           estimativa dada por est_erro=|int_Aprox-int_Aprox2|/15.

%------------------------------------------------------------------------
%             VERIFICAÇÃO DOS PARÂMETROS DE ENTRADA
%------------------------------------------------------------------------
if nargin < 4
    N = 2; % Regra de Simpson simples
end
if nargin<3
    error('Tem de introduzir a função f e os extremos do intervalo')
end
% Verificar se a<b e se N é par
if  a>=b
    error('a deve ser menor que b')
end
if ~(mod(N,2)==0&&N>0)
     error('N deve ser inteiro positivo e par')
end
% Determinação de h e construção do vetor das abcissas
h = (b-a)/N;
abcissas = a:h:b;
%------------------------------------------------------------------------
%                 REGRA DE SIMPSON com N subintervalos
%------------------------------------------------------------------------
y = f(abcissas);          % Vetor dos valores da função dada nos nós
yPar = y(2:2:end-1);      % nos nós de índice par
yImpar = y(3:2:end-2);    % nos nós de índice ímpar
int_Aprox = (h/3)*(y(1)+4*sum(yPar)+2*sum(yImpar)+y(end));
%----------------------------------------------------------------------
%                  ESTIMATIVA PARA O ERRO
%-----------------------------------------------------------------------
if nargout == 2
    if rem(N,4)~=0 
        disp('Para estimar o erro, N tem de ser múltiplo de 4')
        est_erro =[];
    else
        % Cálculo do integral com metade dos subintervalos
            yPar2 = y(3:4:end-1);      
            yImpar2 = y(5:4:end-2);    
            int_Aprox2 = (2*h/3)*(y(1)+4*sum(yPar2)+2*sum(yImpar2)+y(end));

        % Estimativa para o erro
            est_erro = abs(int_Aprox-int_Aprox2)/15;
    end
end