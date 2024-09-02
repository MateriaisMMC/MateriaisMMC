%function lloyd_ex()

% programa baseado no algoritmo de lloyd para fazer "clustering" duma BD
% eventos pertencem a R^2, lidos dum ficheiro BD2.txt;
% metrica usada  euclidiana -> representante do tipo centroide


clear all
clc

M=[];
I=2;     %numero de atributos dum evento

f=fopen('BD2.txt','r')
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

pause

%representacao dos dados 

figure(1)
for i=1:N
  plot(x(i,1),x(i,2),'r*');
  hold on
end

pause

K=2; %numero de clusters
% 
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % representantes - inicializacao
m1x=0
m1y=0
m2x=4 
m2y=5
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Mx=[m1x m2x] % tem conjunto de primeiras coordenadas dos representantes
My=[m1y m2y] % tem conjunto de segundas coordenadas dos representantes
CP=1
it=0
while CP>0.0001 
 P=calcula_particao(Mx,My,x,K)% calculo uma partição usando os representantes anteriores
 [Mx_new,My_new]=calcula_representantes(P,x,N,K)  %calculo representantes usanso particao calculada
 CP=diferenca_representantes(Mx,My,Mx_new,My_new,K) %medida entre novos representantes e antigos
 Mx=Mx_new;
 My=My_new;
 pause
 it=it+1
end
% 
'RESULTADO:'
'*********************'

P
Mx
My

figure(2)
for i=1:length(P)
  if P(i)==1
   plot(x(i,1),x(i,2),'r*');
   hold on
  else
   plot(x(i,1),x(i,2),'k*');
   hold on
  end
end


