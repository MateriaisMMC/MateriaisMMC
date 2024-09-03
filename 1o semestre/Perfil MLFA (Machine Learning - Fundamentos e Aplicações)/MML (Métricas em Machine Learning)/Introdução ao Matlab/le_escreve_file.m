clear all

% f=fopen('experiencia.txt','w');
% for i=1:5
%  for j=1:10
%   fprintf(f,'%f %f %f %f\n',i,j,i+j,i+2*j);
%  end
% end
% fclose(f)


f=fopen('experiencia.txt','r');
i=1
while ~feof(f)
 xx=fscanf(f,'%f %f %f %f\n',4) %le linhas de 4 floats dum file de texto
 x(i,1)=xx(1);
 x(i,2)=xx(2);
 x(i,3)=xx(3);
 x(i,4)=xx(4);
 i=i+1
end
fclose(f)
x
