% Representante tipo medoide ; metrica Euclidiana ; dados de R^2

Dx=[0 2 2 1 -3  ] % componentes x da BD
Dy=[0 1 4 -2 1  ] % componentes y da BD

N=length(Dx) % nº de eventos da BD

figure(1)
plot(Dx,Dy,'r*')
xlabel('x')
ylabel('y')
title('representacao da BD')



% calcula o custo de cada um dos elementos da BD ser representante da BD
% o custo de m ser representante de D é a distancia euclidiana/manhattan de m a todos
% os elementos de D.

custo=zeros(N,1) %vector com N zeros
dist=[];
for i=1:N %para todos os els da BD
 %o representante é (Rx,Ry)=(Dx(i),Dy(i))    
 Rx=Dx(i);
 Ry=Dy(i); %(Rx,Ry) é o elemento "i" da BD   
 for j=1:N 
  %array Dist(i,j) tem distancia de representante (xi,yi) aos elementos da BD 
  dist(i,j)=((Rx-Dx(j))^2+(Ry-Dy(j))^2);% usando metrica euclidiana
  %dist(i,j)=abs(Rx-Dx(j))+abs(Ry-Dy(j));% usando metrica de manhattan
  custo(i)=custo(i)+dist(i,j); %(Rx-Dx(j))^2+(Ry-Dy(j))^2
 end
end

dist
custo


% O representante é o elemento que minimiza o custo

[lista,indice]=sort(custo) %lista tem custos ordenados e indice tem os indices do custo menor para o maior

RepresentanteX=Dx(indice(1))
RepresentanteY=Dy(indice(1))

plot(Dx,Dy,'r*')
hold on

plot(RepresentanteX,RepresentanteY,'bo')