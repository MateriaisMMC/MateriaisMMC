function [d]=calcula_dissemelhanca(Mx,My,x)
% METRICA EUCLIDIANA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Mx=[mx1 mx2] My=[my1 my2]
%x e 1 array com 2 coordenadas 
%d(i,j) tem distancia do evento i ao representate j  

' parametros de calcula dissemelhanca'
Mx
My
x
d=sqrt((Mx-x(1))^2+(My-x(2))^2)
end