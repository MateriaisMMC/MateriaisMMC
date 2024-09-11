function valpol = polDifDiv(x,y,z)

% polDifDiv  Cálculo de valores do polinómio interpolador num conjunto de
%            pontos.
%
%  valpol = polDifDiv(x,y,z) Calcula P(z), onde P é o polinómio interpolador
%      dos pontos (x_i,y_i). O polinómio P (de grau <= n-1, onde n=length(x))
%      é calculado usando a forma de Newton com diferenças divididas;
%      z pode ser um escalar ou um vetor.
%
% INPUT:
%      x: vetor de n componentes distintas (abcissas);
%      y: vetor com a mesma dimensão que x (ordenadas);
%      z: vetor de m componentes com os pontos onde pretendemos calcular
%         os valores do polinómio interpolador.
%
% OUTPUT:
%      valpol: valpol=(P(z_1),...,P(z_m)), onde P é o polinómio de grau 
%              <=n-1 interpolador dos pontos (x_i,y_i).
%--------------------------------------------------------------------------
% NOTA : Necessita da função tabDifDiv
%-------------------------------------------------------------------------

%------------------------------------------------------------------------
%             VERIFICAÇÕES DOS PARÂMETROS DE ENTRADA
%------------------------------------------------------------------------
% As verificações relativas a x e y são feitas quando invocarmos
% a função TABDIFDIV
%--------------------------------------------------------------------
% Uso da função TABDIFDIV para calcular as diferenças divididas
    DD = tabDifDiv(x,y);
%-------------------------------------------
% Extração da primeira linha de DD 
% (que contém as diferenças divididas necessárias ao calculo de valpol)
    dfdv = DD(1,:);
%------------------------------------------------------------------------
%                      CÁLCULO DE valpol
%------------------------------------------------------------------------
n = length(dfdv);
valpol = ones(size(z)); % Inicialização do vetor valpol
valpol(:) = dfdv(n);
for i=n-1:-1:1
    valpol = dfdv(i)+valpol.*(z-x(i)); % Uso da forma encaixada
end