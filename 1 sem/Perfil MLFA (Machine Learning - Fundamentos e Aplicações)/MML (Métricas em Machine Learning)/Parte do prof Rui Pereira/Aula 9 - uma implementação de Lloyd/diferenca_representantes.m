
function CP=diferenca_representantes(Mx,My,Mx_new,My_new,K)

% verifica variacao das coordenadas dos representantes.
% podera ser por exemplo a soma da distancia de (Mx,My) a (Mx_new,My_new)
% para todos os representantes

dist=0;
 for i=1:K
  dist=dist+sqrt((Mx(i)-Mx_new(i))^2+(My(i)-My_new(i))^2);       
 end    
 CP=dist;
end