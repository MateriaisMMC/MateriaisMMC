function b=metGauss(A,b)
%metGauss  resolução de sistema pelo método de Gauss 
%          (com escolha parcial de pivot)
%
% b=metGauss(A,b)   determina a solução de um sistema Ax=b, usando
%                   o método de eliminacao gaussiana com escolha de pivot
%                   para reduzir o sistema à forma triangular; o sistema
%                   triangular é depois resolvido por substituicao inversa,
%                   usando a função subInversa
%
% INPUT:
%    A: matriz quadrada de ordem n (matriz do sistema)
%    b: vetor coluna com n componentes (termos independentes)
%                        
% OUTPUT:
%    b: vetor solução do sistema Ax=b

%------------------------------------------------------------------------
%             Verificação dos parâmetros de entrada
%------------------------------------------------------------------------
% Verificar se a matriz A é quadrada e se b tem a dimensão adequada
[n,m]=size(A); [nb,mb]=size(b);
if  ( n~=m )
    error('Matriz não é quadrada)')
elseif ( nb~=n | mb~=1 )
    error('Vetor b não tem a dimensão adequada')
end
%------------------------------------------------------------------------
%             Processo de Eliminação de Gauss
%------------------------------------------------------------------------
trocas=0;
for k=1:n-1 % Contador de passo
    
    % Escolha parcial de pivot
   
    [mx,r]=max(abs(A(k:n,k))); % determina o elemento de maior módulo das 
                               % linhas k a n da coluna k 
                               % (e a respetiva posição)
                                                       
    l=r+k-1; % é necessário acrescentar k-1 a r porque o elemento desse 
             % vetor na posicao 1, por exemplo, está na linha k, etc.
     if l~=k
         disp(['No passo ',num2str(k),...
             ' da eliminação,o pivot está na linha ',num2str(l)])
     trocas=trocas+1;
    end
                            
    A([k l],:)=A([l k],:); % troca das linhas k e l de A
    b([k l])=b([l k]); % troca das linhas k e l de b

    if A(k,k)==0 %  se todos os elementos da coluna k (abaixo da posição k) 
                 %  forem nulos, A é singular!
       error('matriz singular')
    end
   
    % Eliminação
    
    A(k+1:n,k)=A(k+1:n,k)/A(k,k); % multiplicadores para as linhas k+1 a n
    A(k+1:n,k+1:n)=A(k+1:n,k+1:n)-A(k+1:n,k)*A(k,k+1:n);
    b(k+1:n)=b(k+1:n)-A(k+1:n,k)*b(k);
end
trocas;
if A(n,n)==0
    error('Matriz singular')
end
%---------------------------------------------------------------------
%             Substituição inversa
%------------------------------------------------------------------------
% Aproveitar a parte triangular superior de A
b=subInversa(triu(A),b);
