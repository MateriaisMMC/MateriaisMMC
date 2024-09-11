function DD = tabDifDiv(x,y)

% tabDifDiv Constru��o de tabela de diferen�as divididas.
%
% DD = tabDifDiv(x,y) Constru��o de uma matriz DD cujas colunas s�o
%   as diferen�as divididas relativas a uma tabela de pontos(x_i,y_i).
%
%  INPUT:
%      x: vetor de n componentes distintas (abcissas);
%      y: vetor da mesma dimens�o que x (ordenadas);
%
%   OUTPUT:
%      DD: matriz quadrada de ordem n tendo, na coluna k,  
%          as diferen�as divididas de ordem k-1 relativas aos pontos (x_i,y_i).
%          Na coluna k, como h� apenas n-k+1 diferen�as divididas,
%          os elementos abaixo da posi��o n-k+1 s�o definidos como zero.
%--------------------------------------------------------------------------
%             VERIFICA��ES SOBRE AS ENTRADAS
%--------------------------------------------------------------------------
% Verificar se x e y s�o vetores da mesma dimens�o e se os elementos
% de x s�o distintos
n = length(x);
if length(y) ~= n
   error('Os vetores x e y devem ter a mesma dimens�o') 
elseif ~all(diff(sort(x)))
   error('As abcissas devem ser distintas');
end

%--------------------------------------------------------------------------
% Escrever x e y como vetores coluna
x = x(:);
y = y(:);
%--------------------------------------------------------------------------
%             CONSTRU��O DA MATRIZ DD DAS DIFEREN�AS DIVIDIDAS
%--------------------------------------------------------------------------
DD = zeros(n); % Inicializa��o da matriz DD com zeros
DD(:,1)=y;     % Primeira coluna de DD � o vetor y
% C�lculo recursivo das diferen�as divididas e armazenamento nas colunas de DD
for k = 2:n
    i = 1:n-k+1;
    DD(i,k) = (DD(i+1,k-1)-DD(i,k-1))./(x(i+k-1)-x(i));
end