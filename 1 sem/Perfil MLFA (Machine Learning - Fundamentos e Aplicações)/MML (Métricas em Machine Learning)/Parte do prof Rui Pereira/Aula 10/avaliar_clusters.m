%%%%%%%%%%%%%%%%%%%%%%%%%
%AVALIAR CLUSTERS
%%%%%%%%%%%%%%%%%%%%%%%%%


clear all
clc

M=[];
I=2;     %numero de atributos dum evento

f=fopen('BD.txt','r')
i=1
while ~feof(f)
  xx=fscanf(f,'%f %f\n',2); %le linhas pares de valores da BD xx(1) - primeira coord;xx(2) - segunda corod.
  for j=1:I
   x(i,j)=xx(j); %x(i,j) é coordenada j do evento i 
  end
  i=i+1;
end
fclose(f);
'valores lidos'
x
N=i-1



%representacao dos dados 

figure(1)
for i=1:N
  plot(x(i,1),x(i,2),'r*');
  hold on
end
xlabel('x')
ylabel('y')



% representante do tipo centroide com métrica eucliana
cx=0;
cy=0;
for i=1:N
  cx=cx+x(i,1);
  cy=cy+x(i,2);
end
Rx=(1/N)*cx;
Ry=(1/N)*cy;

plot(Rx,Ry,'ko')
hold on

% Dissemelhança média do cluster

D_med=dissemelhanca_media(x,N,Rx,Ry)

% Dissemelhança quadratica média do cluster

D_q=dissemelhanca_quadratica(x,N,Rx,Ry)

%Dissemelhança maxima do cluster :

D_inf=dissemelhanca_max(x,N,Rx,Ry)

%Diametro do cluster

diam=diametro(x,N)




% EM BD2.txt podemos ver 2 clusters - o primeiro cluster com os 10
% primeiros eventos e o cluster 2 com os 7 eventos seguintes.

% NOTA vamos colocar os valores desta nova BD na variável xis

f2=fopen('BD2.txt','r')
i=1
xx=[];
while ~feof(f2)
  xx=fscanf(f2,'%f %f\n',2); %le linhas pares de valores da BD xx(1) - primeira coord;xx(2) - segunda corod.
  for j=1:I
   xis(i,j)=xx(j); %xis(i,j) é coordenada j do evento i 
  end
  i=i+1;
end
fclose(f2);

N2=length(xis)

%representacao dos dados de BD2.txt com N2 eventos

figure(2)
for i=1:N2
  plot(xis(i,1),xis(i,2),'r*');
  hold on
end
xlabel('x')
ylabel('y')

%vemos que os 10 primeiros elementos pertencem a um cluster e os
%seguintes a outro cluster. Podemos definir 2 arrays C1=[1 2 3 4 5 6 7 8 9 10]
% C2=[11 12 13 14 15 16 17] com os índices dos elementos que pertencem
% respectivamente ao primeiro e segundo clusters

C1=[1 2 3 4 5 6 7 8 9 10]
C2=[11 12 13 14 15 16 17]

% Calculemos a single linkage entre C1 e C2
% Notar que corresponde à menor distância entre elementos de C1 e de C2

sl=calcula_single_linkage(C1,C2,xis)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function D_med=dissemelhanca_media(x,N,Rx,Ry)

dmed=0;
for i=1:N
 dmed=dmed+euclid(x(i,1),x(i,2),Rx,Ry);
end    

D_med=dmed/N;

end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function D_q=dissemelhanca_quadratica(x,N,Rx,Ry)

dmed=0;
for i=1:N
 dmed=dmed+euclid(x(i,1),x(i,2),Rx,Ry)^2;
end    

dmed=dmed/N;
D_q=sqrt(dmed);
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


function D_inf=dissemelhanca_max(x,N,Rx,Ry)

d=[];
for i=1:N
 d(i)=euclid(x(i,1),x(i,2),Rx,Ry);
end

D_inf=max(d);
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


function diam=diametro(x,N)

d=[];
for i=1:N
 for j=1:N   
  d(i,j)=euclid(x(i,1),x(i,2),x(j,1),x(j,2));
 end
end

diam=max(max(d));

end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function sl=calcula_single_linkage(C1,C2,xis)
C1
C2
for i=1:length(C1)
 for j=1:length(C2)
   d(i,j)=euclid(xis(C1(i),1),xis(C1(i),2),xis(C2(j),1),xis(C2(j),2));  
 end
end
d
sl=min(min(d));

end
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

function d=euclid(x1,y1,x2,y2)

d=sqrt((x1-x2)^2+(y1-y2)^2);

end