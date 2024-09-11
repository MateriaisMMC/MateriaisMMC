function DD = tabDifDiv(x,y)

% tabDifDiv Construção de tabela de diferenças divididas.
%
% DD = tabDifDiv(x,y) Construção de uma matriz DD cujas colunas são
%   as diferenças divididas relativas a uma tabela de pontos(x_i,y_i).
%
%  INPUT:
%      x: vetor de n componentes distintas (abcissas);
%      y: vetor da mesma dimensão que x (ordenadas);
%
%   OUTPUT:
%      DD: matriz quadrada de ordem n tendo, na coluna k,  
%          as diferenças divididas de ordem k-1 relativas aos pontos (x_i,y_i).
%          Na coluna k, como há apenas n-k+1 diferenças divididas,
%          os elementos abaixo da posição n-k+1 são definidos como zero.
%--------------------------------------------------------------------------
%             VERIFICAÇÕES SOBRE AS ENTRADAS
%--------------------------------------------------------------------------
% Verificar se x e y são vetores da mesma dimensão e se os elementos
% de x são distintos
n = length(x);
if length(y) ~= n
   error('Os vetores x e y devem ter a mesma dimensão') 
elseif ~all(diff(sort(x)))
   error('As abcissas devem ser distintas');
end

%--------------------------------------------------------------------------
% Escrever x e y como vetores coluna
x = x(:);
y = y(:);
%--------------------------------------------------------------------------
%             CONSTRUÇÃO DA MATRIZ DD DAS DIFERENÇAS DIVIDIDAS
%--------------------------------------------------------------------------
DD = zeros(n); % Inicialização da matriz DD com zeros
DD(:,1)=y;     % Primeira coluna de DD é o vetor y
% Cálculo recursivo das diferenças divididas e armazenamento nas colunas de DD
for k = 2:n
    i = 1:n-k+1;
    DD(i,k) = (DD(i+1,k-1)-DD(i,k-1))./(x(i+k-1)-x(i));
end