function b=metGauss(A,b)
%metGauss  resolu��o de sistema pelo m�todo de Gauss 
%          (com escolha parcial de pivot)
%
% b=metGauss(A,b)   determina a solu��o de um sistema Ax=b, usando
%                   o m�todo de eliminacao gaussiana com escolha de pivot
%                   para reduzir o sistema � forma triangular; o sistema
%                   triangular � depois resolvido por substituicao inversa,
%                   usando a fun��o subInversa
%
% INPUT:
%    A: matriz quadrada de ordem n (matriz do sistema)
%    b: vetor coluna com n componentes (termos independentes)
%                        
% OUTPUT:
%    b: vetor solu��o do sistema Ax=b

%------------------------------------------------------------------------
%             Verifica��o dos par�metros de entrada
%------------------------------------------------------------------------
% Verificar se a matriz A � quadrada e se b tem a dimens�o adequada
[n,m]=size(A); [nb,mb]=size(b);
if  ( n~=m )
    error('Matriz n�o � quadrada)')
elseif ( nb~=n | mb~=1 )
    error('Vetor b n�o tem a dimens�o adequada')
end
%------------------------------------------------------------------------
%             Processo de Elimina��o de Gauss
%------------------------------------------------------------------------
trocas=0;
for k=1:n-1 % Contador de passo
    
    % Escolha parcial de pivot
   
    [mx,r]=max(abs(A(k:n,k))); % determina o elemento de maior m�dulo das 
                               % linhas k a n da coluna k 
                               % (e a respetiva posi��o)
                                                       
    l=r+k-1; % � necess�rio acrescentar k-1 a r porque o elemento desse 
             % vetor na posicao 1, por exemplo, est� na linha k, etc.
     if l~=k
         disp(['No passo ',num2str(k),...
             ' da elimina��o,o pivot est� na linha ',num2str(l)])
     trocas=trocas+1;
    end
                            
    A([k l],:)=A([l k],:); % troca das linhas k e l de A
    b([k l])=b([l k]); % troca das linhas k e l de b

    if A(k,k)==0 %  se todos os elementos da coluna k (abaixo da posi��o k) 
                 %  forem nulos, A � singular!
       error('matriz singular')
    end
   
    % Elimina��o
    
    A(k+1:n,k)=A(k+1:n,k)/A(k,k); % multiplicadores para as linhas k+1 a n
    A(k+1:n,k+1:n)=A(k+1:n,k+1:n)-A(k+1:n,k)*A(k,k+1:n);
    b(k+1:n)=b(k+1:n)-A(k+1:n,k)*b(k);
end
trocas;
if A(n,n)==0
    error('Matriz singular')
end
%---------------------------------------------------------------------
%             Substitui��o inversa
%------------------------------------------------------------------------
% Aproveitar a parte triangular superior de A
b=subInversa(triu(A),b);
