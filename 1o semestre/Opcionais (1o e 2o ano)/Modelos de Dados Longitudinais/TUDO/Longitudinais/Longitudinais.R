#Modelos longitudinais

#06/10

pressao<-read.csv2("dados_turma.csv", header=TRUE)
pressao
#dados em formato wide

#Grafico da distribuicao da idade e das variaveis
summary(pressao$Sexo)
pressao$Sexo=as.factor(pressao$Sexo)
str(dados)

hist(pressao$Idade, breaks=30, freq=FALSE)

summary(c(pressao$Max_t1, pressao$Max_t2, pressao$Max_t3))

plot(0,0,xlim=c(1,3), ylim=c(80,140), type="n", xlab="momentos", ylab="Maxima")
points(rep(1,20), pressao$Max_t1, col="red")
points(rep(2,20), pressao$Max_t2, col="blue")
points(rep(3,20), pressao$Max_t3, col="green")

#os dados no momento 1 tem maior variancia, mas nao sabemos quem é quem, 
#temos de acrescentar as linhas 
for(i in 1:20){
  lines(c(1,2,3), 
        c(pressao$Max_t1[i], pressao$Max_t2[i], pressao$Max_t3[i]) )
  print(i)
  }

#Ver os 2 graficos lado a lado
par(mfrow=c(1,2))

plot(0,0,xlim=c(1,3), ylim=c(80,140), type="n", xlab="momentos", ylab="Maxima")
points(rep(1,20), pressao$Max_t1, col="red")
points(rep(2,20), pressao$Max_t2, col="blue")
points(rep(3,20), pressao$Max_t3, col="green")

#----

plot(0,0,xlim=c(1,3), ylim=c(80,140), type="n", xlab="momentos", ylab="Maxima")
points(rep(1,20), pressao$Max_t1, col="red")
points(rep(2,20), pressao$Max_t2, col="blue")
points(rep(3,20), pressao$Max_t3, col="green")

for(i in 1:20){
  lines(c(1,2,3), 
        c(pressao$Max_t1[i], pressao$Max_t2[i], pressao$Max_t3[i]) )
  print(i)
}


#alternativa ao loop feito com for

plot(0,0,xlim=c(1,3), ylim=c(80,140), type="n", xlab="momentos", ylab="Maxima")
points(rep(1,20), pressao$Max_t1, col="red")
points(rep(2,20), pressao$Max_t2, col="blue")
points(rep(3,20), pressao$Max_t3, col="green")

by(pressao,pressao$ID, function(x){
  lines(c(1,2,3), 
        c(x$Max_t1, x$Max_t2, x$Max_t3) )
  print(i)
})


# PASSAR BASE DE DADOS DO FORMATO WIDE PARA FORMATO LONG 

pressao.long=reshape (pressao, direction = "long", varying = list(Max=c(4,6,8),
                           Min=c(5,7,9)));pressao.long
#varying sao as colunas q variam com o tempo
names(pressao.long)[c(5,6)]=c("Max","Min")

pressao.long=pressao.long[order(pressao.long$ID),] #por juntos por id

row.names(pressao.long)=1:(dim(pressao.long)[1]) #numerar as linhas de 1 a 60
pressao.long

par(mfrow=c(1,2))

plot(pressao.long$time, pressao.long$Max)
by(pressao.long, pressao.long$ID, function(x){
  lines(x$time, x$Max) 
})

plot(pressao.long$time, pressao.long$Min)
by(pressao.long, pressao.long$ID, function(x){
  lines(x$time, x$Min) 
})


# Especificar os tempos de observacao
pressao.long2=reshape (pressao, direction = "long", varying = list(Max=c(4,6,8),
          Min=c(5,7,9)), times =c(0,4,10))

# PASSAR BASE DE DADOS DO FORMATO LONG PARA FORMATO WIDE

pressao.wide=reshape(pressao.long, direction = "wide", v.names = c("Max_t1", "Min_t1"), timevar = "time")


#20/10

library(MASS)
?mvrnorm
set.seed(100)
y=rnorm(100, 0, 2);y # 100 realizacoes de media 5 e desvio 2

set.seed(100)
z=mvrnorm(1, rep(0,100), 4*diag(100)) #o y e o z é a mesma coisa pq iid

cbind(y,z[100:1])
plot(y, z[100:1])

library(car)
data(cars)
cars
model=lm(dist~speed, data=cars)
summary(model)

names(model)
model.matrix(model) #matriz de desenho

model=lm(dist~ -1 + speed, data=cars) #tiramos o beta 0 


#27/10

data(cars)
cars
head(cars)
model=lm(speed~dist, data =cars)# o lm assume independencia entre as observacoes
summary(model)
vcov(model)#matriz var cov dos betas ^
sqrt(diag(vcov(model)))#std error do summary

# 03/11

pressao<-read.csv2("dados_turma.csv", header=TRUE)
pressao
#dados em formato wide


# PASSAR BASE DE DADOS DO FORMATO WIDE PARA FORMATO LONG 
pressao.long=reshape (pressao, direction = "long", varying = list(Max=c(4,6,8),
                                                                  Min=c(5,7,9)));pressao.long

#varying sao as colunas q variam com o tempo
names(pressao.long)[c(5,6)]=c("Max","Min")

pressao.long=pressao.long[order(pressao.long$ID),] #por juntos por id

row.names(pressao.long)=1:(dim(pressao.long)[1]) #numerar as linhas de 1 a 60
pressao.long

model=lm(Max ~Idade + Sexo, data =pressao.long)
summary(model)
vcov(model) #var=sigma^2*Dtransposto*D
sqrt(diag(vcov(model)))
#Neste modelo, usando a funçao lm estamos assumir que todas as observaçoes sao independentes
#o que está errado, cada pessoa tem 3 observaçoes dela propria que estao as 3 correlacionadas
#e por isso os nossos std.errors e pvalues estao errados pq estao assumir todas as observaçoes independentes


plot(pressao.long$Idade, pressao.long$Max)
points(pressao.long$Idade[pressao.long$Sexo=="F"], 
        pressao.long$Max[pressao.long$Sexo=="F"], col="blue", pch=19)
points(pressao.long$Idade[pressao.long$Sexo=="M"], 
       pressao.long$Max[pressao.long$Sexo=="M"], col="red", pch=19)
labels(locator(1), c("Male", "Female"), pch=c(19,19), col=c("red","blue"))

#Para resolver o problema da independencia precisamos de calcular a correlaçao e a variancia 
#das observaçoes no tempo 1 com as observacoes no tempo 2 (agora sim, sao independentes)
cov(pressao.long$Max[pressao.long$time==1], 
    pressao.long$Max[pressao.long$time==2], use="complete.obs") #use="complete.obs" pa tirar os N.A

#das observaçoes no tempo 1 com as observacoes no tempo 3
cov(pressao.long$Max[pressao.long$time==1],
    pressao.long$Max[pressao.long$time==3], use="complete.obs")

#das observaçoes no tempo 2 com as observacoes no tempo 3 
cov(pressao.long$Max[pressao.long$time==2],
    pressao.long$Max[pressao.long$time==3], use="complete.obs")

#Calcular a variancia das observaçoes no tempo 1
var(pressao.long$Max[pressao.long$time==1], na.rm = TRUE) #na.rm=T para tirar os NA

#Calcular a variancia das observaçoes no tempo 2
var(pressao.long$Max[pressao.long$time==2], na.rm = TRUE)

#Calcular a variancia das observaçoes no tempo 3
var(pressao.long$Max[pressao.long$time==3], na.rm = TRUE)


#Para determinar os estimadores robustos dos S.E. de beta chapeu, atraves de comandos

library(gee)
modelo.gee= gee(Max ~Idade + Sexo, data =pressao.long, id=ID) #id=coluna na bd na qual existe medidas repetidas
summary(modelo.gee)

#IC para sexo masculino:

#considerando o estimador naive
9.0001940+c(1,-1)*1.96*2.7794501

#considerando o estimador robusto
9.0001940+c(1,-1)*1.96*3.5192254


#IC para idade:

#considerando o estimador naive
0.1687984 +c(1,-1)*1.96*0.1730602 

#considerando o estimador robusto
0.1687984 +c(1,-1)*1.96*0.1416347  

#10/11

pressao<-read.csv2("dados_turma.csv", header=TRUE)
pressao


# PASSAR BASE DE DADOS DO FORMATO WIDE PARA FORMATO LONG 
pressao.long=reshape (pressao, direction = "long", varying = list(Max=c(4,6,8),
                                                                  Min=c(5,7,9)));pressao.long

#varying sao as colunas q variam com o tempo
names(pressao.long)[c(5,6)]=c("Max","Min")

pressao.long=pressao.long[order(pressao.long$ID),] #por juntos por id

row.names(pressao.long)=1:(dim(pressao.long)[1]) #numerar as linhas de 1 a 60
pressao.long

#das observaçoes no tempo 1 com as observacoes no tempo 2 (agora sim, sao independentes)
cov(pressao.long$Max[pressao.long$time==1], 
    pressao.long$Max[pressao.long$time==2], use="complete.obs") #use="complete.obs" pa tirar os N.A

#das observaçoes no tempo 1 com as observacoes no tempo 3
cov(pressao.long$Max[pressao.long$time==1],
    pressao.long$Max[pressao.long$time==3], use="complete.obs")

#das observaçoes no tempo 2 com as observacoes no tempo 3 
cov(pressao.long$Max[pressao.long$time==2],
    pressao.long$Max[pressao.long$time==3], use="complete.obs")

#Calcular a variancia das observaçoes no tempo 1
var(pressao.long$Max[pressao.long$time==1], na.rm = TRUE) #na.rm=T para tirar os NA

#Calcular a variancia das observaçoes no tempo 2
var(pressao.long$Max[pressao.long$time==2], na.rm = TRUE)

#Calcular a variancia das observaçoes no tempo 3
var(pressao.long$Max[pressao.long$time==3], na.rm = TRUE)

# ajustar o modelo com medidas repetidas correlacionadas de um mesmo individuo
library(nlme)
?gls
model.gls.unst=gls(Max~Idade+Sexo+time, 
                   data = pressao.long, correlation = corSymm(form = ~1|id), 
                   method = "ML", na.action = na.exclude)

#corSymm para dizer quais sao as variavis que sao do mesmo individuo

summary(model.gls.unst)

#Correlation Structure: General 
#Formula: ~1 | id 
#Parameter estimate(s):
#  Correlation: 
#  1     2    
#2 0.447      
#3 0.335 0.511

#da nos a matriz de correlacao devia dar o mesmo que a correlacao mas nao da prof nao sabe pq

#Correlacao
#das observaçoes no tempo 1 com as observacoes no tempo 2
cor(pressao.long$Max[pressao.long$time==1], 
    pressao.long$Max[pressao.long$time==2], use="complete.obs") #use="complete.obs" pa tirar os N.A

#das observaçoes no tempo 1 com as observacoes no tempo 3
cor(pressao.long$Max[pressao.long$time==1],
    pressao.long$Max[pressao.long$time==3], use="complete.obs")

#das observaçoes no tempo 2 com as observacoes no tempo 3 
cor(pressao.long$Max[pressao.long$time==2],
    pressao.long$Max[pressao.long$time==3], use="complete.obs")

#24/11
# Ficha 2

pressao<-read.csv2("dados_turma.csv", header=TRUE)
pressao


# PASSAR BASE DE DADOS DO FORMATO WIDE PARA FORMATO LONG 
pressao.long=reshape (pressao, direction = "long", varying = list(Max=c(4,6,8),
                                                                  Min=c(5,7,9)));pressao.long

#varying sao as colunas q variam com o tempo
names(pressao.long)[c(5,6)]=c("Max","Min")

pressao.long=pressao.long[order(pressao.long$ID),] #por juntos por id

row.names(pressao.long)=1:(dim(pressao.long)[1]) #numerar as linhas de 1 a 60
pressao.long


library(gee)
modelo.gee= gee(Max ~Idade + Sexo, data =pressao.long, id=ID) #id=coluna na bd na qual existe medidas repetidas
summary(modelo.gee)

#IC para sexo masculino:

#considerando o estimador naive
9.0001940+c(1,-1)*1.96*2.7794501

#considerando o estimador robusto
9.0001940+c(1,-1)*1.96*3.5192254

#IC para idade:

#considerando o estimador naive
0.1687984 +c(1,-1)*1.96*0.1730602 

#considerando o estimador robusto
0.1687984 +c(1,-1)*1.96*0.1416347 

modelo.lm<-lm(Max ~Idade + Sexo, data =pressao.long)
summary(modelo.lm)

#p-valor dos naive tb pode ser calculado pela formula:
2*(1-pnorm(17.773))
2*(1-pnorm(0.975))
2*(1-pnorm(3.238)) 

#p-valor dos robustos
2*(1-pnorm(18.460881))
2*(1-pnorm(1.191787))
2*(1-pnorm(2.557436))


# ajustar o modelo com medidas repetidas correlacionadas de um mesmo individuo
library(nlme)
?gls
model.gls.unst=gls(Max~Idade+Sexo+time, 
                   data = pressao.long, correlation = corSymm(form = ~1|id), 
                   method = "ML", na.action = na.exclude)

#corSymm para dizer quais sao as variavis que sao do mesmo individuo

summary(model.gls.unst)

sqrt(163.32)
sqrt(60.73)
sqrt(95.88)

anova(model.gls.unst)