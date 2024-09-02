% C={x1,x2,x3,x4,x5} onde x1=(0,0); x2=(2,1);x3=(2,4);x4=(1,-2);x5=(-2,4)
% Representante de C usando Metrica Euclidiana Nota: os evento pertence a R^2 

Cx=[0 2  2 1 -2] %Cx guarda as primeira coordenadas dos eventos de C

Cy=[0 1 4  -2 4] %Cy guarda as segundas coordenadas dos eventos de C

N=length(Cx) % Número de eventos de C

Soma_Cx=0;
for i=1:N
 Soma_Cx=Soma_Cx+Cx(i);
end
Soma_Cx

Soma_Cy=0;
for i=1:N
 Soma_Cy=Soma_Cy+Cy(i);
end
Soma_Cy

m_x=Soma_Cx/N

m_y=Soma_Cy/N
