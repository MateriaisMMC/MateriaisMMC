function valpol = polDifDiv(x,y,z)

% polDifDiv  C�lculo de valores do polin�mio interpolador num conjunto de
%            pontos.
%
%  valpol = polDifDiv(x,y,z) Calcula P(z), onde P � o polin�mio interpolador
%      dos pontos (x_i,y_i). O polin�mio P (de grau <= n-1, onde n=length(x))
%      � calculado usando a forma de Newton com diferen�as divididas;
%      z pode ser um escalar ou um vetor.
%
% INPUT:
%      x: vetor de n componentes distintas (abcissas);
%      y: vetor com a mesma dimens�o que x (ordenadas);
%      z: vetor de m componentes com os pontos onde pretendemos calcular
%         os valores do polin�mio interpolador.
%
% OUTPUT:
%      valpol: valpol=(P(z_1),...,P(z_m)), onde P � o polin�mio de grau 
%              <=n-1 interpolador dos pontos (x_i,y_i).
%--------------------------------------------------------------------------
% NOTA : Necessita da fun��o tabDifDiv
%-------------------------------------------------------------------------

%------------------------------------------------------------------------
%             VERIFICA��ES DOS PAR�METROS DE ENTRADA
%------------------------------------------------------------------------
% As verifica��es relativas a x e y s�o feitas quando invocarmos
% a fun��o TABDIFDIV
%--------------------------------------------------------------------
% Uso da fun��o TABDIFDIV para calcular as diferen�as divididas
    DD = tabDifDiv(x,y);
%-------------------------------------------
% Extra��o da primeira linha de DD 
% (que cont�m as diferen�as divididas necess�rias ao calculo de valpol)
    dfdv = DD(1,:);
%------------------------------------------------------------------------
%                      C�LCULO DE valpol
%------------------------------------------------------------------------
n = length(dfdv);
valpol = ones(size(z)); % Inicializa��o do vetor valpol
valpol(:) = dfdv(n);
for i=n-1:-1:1
    valpol = dfdv(i)+valpol.*(z-x(i)); % Uso da forma encaixada
end