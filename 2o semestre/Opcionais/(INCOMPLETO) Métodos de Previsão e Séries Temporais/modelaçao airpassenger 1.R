### Modela??o da base de dados AirPassengers
?AirPassengers

str(AirPassengers)

dados<-ts(AirPassengers[1:120], start = c(1949,1), frequency = 12)
#deixar para teste os seguintes dados:
dados_comp<-AirPassengers[121:144]
windows()
ts.plot(dados,main="Monthly Airline Passenger Numbers 1949-1958")
# ou plot(dados, main="Monthly Airline Passenger Numbers 1949-1958")
#? not?ria a existencia de tend?ncia linear crescente 

decompose(dados)
plot(decompose(dados))
#? not?ria a exist?ncia de tend?ncia, sazonalidade e diferente vari?ncia 


####################### Utilizando a Fun??o BoxCox.lambda ####################

######## Estabilizar a vari?ncia ############

#Para encontrar o lambda necess?rio para realizar a metodologia Box-Jenkins
library(forecast)
lambda<-BoxCox.lambda(dados, lower=-1, method = "loglik") #lambda=0.1
lambda
dados_est<-BoxCox(dados, lambda = lambda)
windows()
plot(dados_est, ylab="dados") #vari?ncia estabilizada


n1 = length(dados_est); n1 #120
par(mfrow=c(1,2))
acf(dados_est, lag.max = 0.25*n1)
pacf(dados_est, lag.max = 0.25*n1)

## vamos modelar a tend?ncia linear
time=seq(1,n1)
time
#ou
time=seq_along(dados_est)
time
#time2=time^2
#time3=time^3
resultados1=lm(dados_est~1+time)
resultados1
summary(resultados1)
#n?o precisa de colocar 1+ pois estima na mesma a constante
resultados1=lm(dados_est~time)
resultados1
#tend?ncia quadr?tica seria o modelo:
#resultados1=lm(dados_est~1+time+time2)
#tend?ncia c?bica seria o modelo:
#resultados1=lm(dados_est~1+time+time2+time3), etc


plot(time,c(dados_est),type="l")
abline(resultados1)
trend=resultados1$fitted.values
dados1=resultados1$residuals
dados1
plot(ts(dados1))
##ou
plot(ts(resultados1$residuals))
##representar os dados antes e depois de retirar a tend?ncia
par(mfrow=c(2,1))
plot(time,dados_est,main="dados_est")
lines(time,trend,col=2)
plot(time,dados1,main="Depois da tend?ncia ajustada")
#etc....
n1 = length(dados_est)
n1
period = 12
aux = seq(1,period)
aux
whichMonth = rep(aux, (n1/period)+1)
whichMonth
whichMonth = whichMonth[1:n1]
whichMonth

jan = dados_est[whichMonth == 1]
jan
fev = dados_est[whichMonth == 2]
mar = dados_est[whichMonth == 3] 
abr = dados_est[whichMonth == 4]
mai = dados_est[whichMonth == 5]
jun = dados_est[whichMonth == 6]
jul = dados_est[whichMonth == 7]
ago = dados_est[whichMonth == 8]
set = dados_est[whichMonth == 9]
out = dados_est[whichMonth == 10]
nov = dados_est[whichMonth == 11]
dez = dados_est[whichMonth == 12]

par(mfrow=c(3,4))
ts.plot(jan,  main="Janeiro")
ts.plot(fev,  main="Fevereiro")
ts.plot(mar,  main="Mar?o")
ts.plot(abr,  main="Abril")
ts.plot(mai,  main="Maio")
ts.plot(jun,  main="Junho")
ts.plot(jul,  main="Julho")
ts.plot(ago,  main="Agosto")
ts.plot(set,  main="Setembro")
ts.plot(out,  main="Outubro")
ts.plot(nov,  main="Novembro")
ts.plot(dez,  main="Dezembro")

plot(dados1~as.factor(whichMonth))
#alternativa para modelar a sazonalidade via vari?veis indicatrizes
dados1
whichMonth
resultados2=lm(dados1~-1+factor(whichMonth))
resultados2
summary(resultados2)

#Remover o factor level 4 (n?o significativo) -> corresponde ao m?s de abril
resultados3=lm(dados1~-1+factor(whichMonth, exclude=c('4') ))
resultados3
summary(resultados3)

#Remover o factor level 5 (n?o significativo) -> corresponde ao m?s de maio
resultados4=lm(dados1~-1+factor(whichMonth, exclude=c('4','5') ))
resultados4
summary(resultados4)


sazonalidade=resultados4$fitted.values
dados2=resultados4$residuals
plot(dados_est,main="Sem tend e sazonalidade")
# library(forecast)
# seasonplot(serie1, col=rainbow(18), year.labels=TRUE)
#alternativa para modelar a sazonalidade via vari?veis indicatrizes

d1=1*(whichMonth == 1)
d2=1*(whichMonth == 2)
d3=1*(whichMonth == 3)
d4=1*(whichMonth == 4)
d5=1*(whichMonth == 5)
d6=1*(whichMonth == 6)
d7=1*(whichMonth == 7)
d8=1*(whichMonth == 8)
d9=1*(whichMonth == 9)
d10=1*(whichMonth == 10)
d11=1*(whichMonth == 11)
d12=1*(whichMonth == 12)
res1=lm(dados1~-1+d1+d2+d3+d4+d5+d6+d7+d8+d9+d10+d11+d12)
res1
summary(res1)
#Remover o factor level 4 (n?o significativo) -> corresponde ao m?s de abril
res2=lm(dados1~-1+d1+d2+d3+d5+d6+d7+d8+d9+d10+d11+d12)
res2
summary(res2)
#Remover o factor level 5 (n?o significativo) -> corresponde ao m?s de maio
res3=lm(dados1~-1+d1+d2+d3+d6+d7+d8+d9+d10+d11+d12)
res3
summary(res3)
########################## defini??o das vari?veis

t = 1:n1
cos12 = cos(2 * pi * 1 * t / 12)
cos6 = cos(2 * pi * 2 * t / 12)
cos4 = cos(2 * pi * 3 * t / 12)
cos3 = cos(2 * pi * 4 * t / 12)
cos2.4 = cos(2 * pi * 5 * t / 12)
cos2 = cos(2 * pi * 6 * t/12)
sin12 = sin(2 * pi * 1 * t / 12)
sin6 = sin(2 * pi * 2 * t / 12)
sin4 = sin(2 * pi * 3 * t / 12)
sin3 = sin(2 * pi * 4 * t / 12)
sin2.4 = sin(2 * pi * 5 * t / 12)
sin2 = sin(2 * pi * 6 * t / 12)
resultados3=lm(dados1~-1+cos12+cos6+cos4+cos3+cos2.4+cos2+sin12+sin6+sin4+sin3+sin2.4+sin2)
resultados3
summary(resultados3)
resultados4=lm(dados1~-1+cos12+cos6+cos4+cos3+cos2.4+sin12+sin6+sin4+sin3+sin2.4)
resultados4
summary(resultados4)
resultados5=lm(dados1~-1+cos12+cos6+cos4+cos3+sin12+sin6+sin4+sin3)
resultados5
summary(resultados5)
resultados6=lm(dados1~-1+cos12+cos6+cos3+sin12+sin6+sin3)
resultados6
summary(resultados6)
dados3=resultados6$residuals
par(mfrow=c(2,1))
plot(time,dados3,main="Sem tend e sazonalidade")

#alternativa ? modelar em simult?neo a tendencia e a sazonalidade
#mas para isso o modelo n?o pode ter constante
#gosto pessoalmente mais trabalhar com "dummies" e come?o ent?o
simultaneo1=lm(dados_est~-1+time+d1+d2+d3+d4+d5+d6+d7+d8+d9+d10+d11+d12)
simultaneo1
summary(simultaneo1)
#? tudo significativo o que "funciona" muito melhor, da? dever-se modelar em simult?neo tend+sazon
#outra forma alternativa de modelar em simult?neo ? com harm?nicos
#que neste caso n?o vai funcionar bem
resultadosglobal1=lm(dados_est~-1+time+cos12+cos6+cos4+cos3+cos2.4+cos2+sin12+sin6+sin4+sin3+sin2.4+sin2)
resultadosglobal1
summary(resultadosglobal1)
dadosfinais=resultadosglobal1$residuals
par(mfrow=c(2,1))
plot(time,dadosfinais,main="Sem tend e sazonalidade")
#n?o resultou bem com os harm?nicos
############# teste de estacionariedade (raiz unit?ria)

## teste ADF
# H0: Existe pelo menos uma raiz dentro do c?rculo unit?rio (a s?rie n?o ? estacion?ria)
# H1: N?o existem ra?zes dentro do c?rculo unit?rio (a s?rie ? estacion?ria)
## https://www.quora.com/How-do-I-interpret-the-results-in-an-augmented-Dickey-Fuller-test
## rejeita-se H0, ou seja, a s?rie ? estacion?ria, se ET < -1.95 (n?vel 5%)


par(mfrow=c(1,2));plot(dadosfinais);acf(dadosfinais)

## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
n1
p = trunc(12 * (n1/100)^(1/4)); p #maior inteiro que o numero contem

testeADF = ur.df(dadosfinais, lags=p, type="trend")
summary(testeADF)
#dado que -1.391>-3.43, nao podemos rejeitar a hipotese de que pi ou delta=0, devemos procurar aumentar o poder do teste.
#(ou seja, testar se a tendencia ? estatisticamente significativa (phi3)).
#como 2.4015<6.49,podemos rejeitar,logo podemos concluir que o termo da tend?ncia pode ser retirado para
#que o poder do teste fique maior.


testeADF = ur.df(dadosfinais, lags=p, type="drift")
summary(testeADF)
#tt significativo
#-1.8381>tau2, n?o podemos rejeitar H_0
#Para verificar se podemos aumentar o poder do teste (phi1): 1.7614<4.63, assim podemos 
#retirar o termo drift da regress?o de teste.


#-----//------
#Se no teste anterior se concluiu que dever ser utilizado o termo drift, n?o ? necess?rio realizar este teste.
#Caso contr?rio, como aconteceu, temos de aplicar este teste.
testeADF = ur.df(dadosfinais, lags=p)
summary(testeADF)

#como -1.8863>-1.95 conclui-se que n?o podemos rejeitar a hip?tese nula, a s?rie ? n?o estacion?ria
#-----//------


## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
#kpss = ur.kpss(dadosfinais, type="tau")  # se tt significativo no teste ADF
kpss = ur.kpss(dadosfinais, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.1016<0.463
# ET <VC - rejeita-se a hip?tese nula de estacionariedade

## Conclus?o: A s?rie ? n?o estacion?ria.
##O teste ADF deve ser sempre seguido pelo teste KPSS

## NOTA: Quando o teste ADF d? n?o estacion?rio e o teste KPSS d? estacion?rio conclui-se que a s?rie ? n?o estacion?ria.

library(tseries)
adf.test(dadosfinais,k=p)
kpss.test(dadosfinais)#tendo tend?ncia)
kpss.test(dadosfinais,null="Trend") #(n?o tendo tend?ncia)
ALTERNATIVA
pacf(dados_est, lag.max = 0.25*n1)


############# teste de estacionariedade (raiz unit?ria)

## teste ADF
# H0: Existe pelo menos uma raiz dentro do c?rculo unit?rio (a s?rie n?o ? estacion?ria)
# H1: N?o existem ra?zes dentro do c?rculo unit?rio (a s?rie ? estacion?ria)
## https://www.quora.com/How-do-I-interpret-the-results-in-an-augmented-Dickey-Fuller-test
## rejeita-se H0, ou seja, a s?rie ? estacion?ria, se ET < -1.95 (n?vel 5%)


par(mfrow=c(1,2));plot(dados_est);acf(dados_est)

## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
p = trunc(12 * (n1/100)^(1/4)); p #maior inteiro que o numero contem

testeADF = ur.df(dados_est, lags=p, type="trend")
summary(testeADF)
#dado que -0.9184>tau3, nao podemos rejeitar a hipotese de que pi=0, devemos procurar aumentar o poder do teste.
#(ou seja, testar se a tendencia ? estatisticamente significativa (phi3)).
#como 1.9748<6.49, nao podemos rejeitar,logo podemos concluir que o termo da tend?ncia pode ser retirado para
#que o poder do teste fique maior.


testeADF = ur.df(dados_est, lags=p, type="drift")
summary(testeADF)
#tt significativo
#-1.8381>tau2, n?o podemos rejeitar H_0
#Para verificar se podemos aumentar o poder do teste (phi1): 7.1197>4.63
# podemos rejeitar que alpha=0|pi=0, devemos inserir o termo drift da regress?o de teste.


#-----//------
#Como no teste anterior conclui-se que dever ser utilizado o termo drift, n?o ? necess?rio realizar este teste.
testeADF = ur.df(dados_est, lags=p)
summary(testeADF)
#-----//------


## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
kpss = ur.kpss(dados_est, type="tau")  # se tt significativo no teste ADF
#kpss = ur.kpss(dados_est, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.0442<0.146
# ET < VC - n?o se rejeita a hip?tese nula de estacionariedade

## Quando o teste ADF d? n?o estacion?rio e o teste KPSS d? estacion?rio conclui-se que a s?rie ? n?o estacion?ria.
## Conclus?o: A s?rie ? n?o estacion?ria.
############# ordem da diferencia??o d=? (estabilizar tend?ncia)

library(forecast)
ndiffs(dados_est)   # d=1 #sugere quantas diferencia??es vao ter de ser realizadas
nsdiffs(dados_est)    # D=1 #sugere as diferencia?oes da parte sazonal 

dif = arima(dados_est, order=c(0,1,0))
layout(matrix(c(1,1,2,3), 2, byrow=T))
plot(dif$residuals)
acf(dif$residuals, main = "FAC(d=1)", lag.max = 0.25*n1)
pacf(dif$residuals, main = "FACP(d=1)", lag.max = 0.25*n1)


## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
p = trunc(12 * (n1/100)^(1/4)); p


testeADF = ur.df(dif$residuals, lags=p, type="trend")
summary(testeADF)
#-2.8598>-3.43, logo n?o se rejeita H_0, a s?rie ? n?o estacion?ria
#4.7234<6.49, logo o termo da tend?ncia pode ser retirado


testeADF = ur.df(dif$residuals, lags=p, type="drift")
summary(testeADF)
#tt significativo
# -2.5007>-2.88, logo n?o podemos rejeitar a hip?tese nula
#3.128<4.63, logo devemos retirar o termo drift da regress?o de teste.

testeADF = ur.df(dif$residuals, lags=p)
summary(testeADF)
# tt n?o significativo
#-1.1022>-1.95, n?o podemos rejeitar a hip?tese nula, a s?rie ? n?o estacion?ria


## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
#kpss = ur.kpss(dif$residuals, type="tau")  # se tt significativo no teste ADF
kpss = ur.kpss(dif$residuals, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.2353<0.463
#ET<VC --> a s?rie ? estacion?ria

### Conclus?o: A s?rie ainda n?o ? estacion?ria ap?s uma diferencia??o. 


### 2? diferencia?ao


dif2 = arima(dados_est, order=c(0,2,0))
layout(matrix(c(1,1,2,3), 2, byrow=T))
plot(dif2$residuals)
acf(dif2$residuals, main = "FAC(d=1)", lag.max = 0.25*n1)
pacf(dif2$residuals, main = "FACP(d=1)", lag.max = 0.25*n1)


## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
p = trunc(12 * (n1/100)^(1/4)); p


testeADF = ur.df(dif2$residuals, lags=p, type="trend")
summary(testeADF)
#tt nao significativo
#-7.6799<-3.43, logo rejeita.se H_0, a s?rie ? estacion?ria
#29.5363>6.49, logo o termo da tend?ncia pode ser inserido na regress?o de teste.

#-----//------
#j? n?o ? necess?rio fazer estes testes
testeADF = ur.df(dif2$residuals, lags=p, type="drift")
summary(testeADF)

testeADF = ur.df(dif2$residuals, lags=p)
summary(testeADF)
#------//--------

## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
#kpss = ur.kpss(dif$residuals, type="tau")  # se tt significativo no teste ADF
kpss = ur.kpss(dif2$residuals, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.086<0.463
#ET<VC --> a s?rie ? estacion?ria

### Conclus?o: A s?rie ? estacion?ria ap?s duas diferencia??es. 




# definimos d=2
dif2 = dif2$residuals

############## sazonalidade ###################

### determinar s

# atrav?s do periodograma
periodogram=spectrum(as.vector(dados), plot=F)
imax=which.max(periodogram$spec)
periodo=1/periodogram$freq[imax]
periodo #12

# consideramos s=12


### determinar D, P e Q
auto.arima(dif2)
#Modelo sugerido: ARIMA(4,0,1)(0,1,1)[12] 

# Fazer P=1, D=Q=0. Se coeficiente AR pr?ximo de 1, ent?o D=1 


seas1 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(1,0,0), period = 12))
summary(seas1)
#sar1 pr?ximo de 1 por isso definimos D=1

seas2 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(1,1,0), period = 12))
summary(seas2)
BIC(seas2)
#AIC= -143.82, BIC= -138.494

seas3 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(0,1,1), period = 12))
summary(seas3)
BIC(seas3)
#AIC= -155.47, BIC= -150.143

seas4 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(1,1,1), period = 12))
summary(seas4)
BIC(seas4)
#AIC= -153.81, BIC= -145.8216

seas5 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(2,1,1), period = 12))
summary(seas5)
BIC(seas5)
#AIC= -152.68, BIC= -142.024

seas6 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(1,1,2), period = 12))
summary(seas6)
BIC(seas6)
#AIC= -153.01, BIC= -142.3588

### Modelo com menor AIC e menor BIC: P=0, D=1, Q=1
# os coeficientes s?o significativamente diferentes de 0?
seas3$coef[1] + c(-1,1) * qnorm(0.975) * sqrt(seas3$var.coef[1,1]) # = (-0.8513659; -0.4511293) -> sim
#coeficiente estatisticamente significativo



###################### determinar p e q

m0 = arima(dados_est, order = c(0,2,0), seasonal = list(order = c(0,1,1), period = 12))
summary(m0)
BIC(m0)
#AIC= -155.47, BIC= -150.143

m1 = arima(dados_est, order = c(1,2,0), seasonal = list(order = c(0,1,1), period = 12))
summary(m1)
BIC(m1)
#AIC= -210.94, BIC= -202.9497

m2 = arima(dados_est, order = c(0,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(m2)
BIC(m2)
#AIC= -247.56, BIC= -239.5705

m3 = arima(dados_est, order = c(2,2,2), seasonal = list(order = c(0,1,1), period = 12))
summary(m3)
BIC(m3)
#AIC= -252.52, BIC= -236.5405


#"current model": ARIMA(2,2,2)(0,1,1)[12] com AIC= -252.52, BIC= -236.5405

#varia??es do "current model": 

m4 = arima(dados_est, order = c(1,2,2), seasonal = list(order = c(0,1,1), period = 12))
summary(m4)
BIC(m4)
#AIC= -253.26, BIC= -239.9463

m5 = arima(dados_est, order = c(1,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(m5)
BIC(m5)
#AIC= -255.24, BIC= -244.5824

m6 = arima(dados_est, order = c(2,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(m6)
BIC(m6)
#AIC= -253.24, BIC= -239.9269

##Modelo Escolhido: ARIMA(1,2,1)(0,1,1)[12]
modelo = arima(dados_est, order = c(1,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(modelo)

modelo$coef[1] + c(-1,1) * qnorm(0.975) * sqrt(modelo$var.coef[1,1]) #(-0.4820788, -0.1161660)
modelo$coef[2] + c(-1,1) * qnorm(0.975) * sqrt(modelo$var.coef[2,2]) #(-1.1272320, -0.8687378)
modelo$coef[3] + c(-1,1) * qnorm(0.975) * sqrt(modelo$var.coef[3,3]) #(-0.6760193, -0.3253271)
#coeficientes significativos (porque o zero n?o pertence ao intervalo)

## AVALIAR SE OS RES?DUOS APRESENTAM UM COMPORTAMENTO SEMELHANTE A UM RU?DO BRANCO 
res = modelo$residuals

layout(matrix(c(1,2,3,4),2,byrow=T))
plot(res, main="Representa??o gr?fica dos res?duos", ylab="")
hist(res, freq=F, main="Histograma dos res?duos", xlab="res?duos", ylab="frequ?ncia relativa")
curve(dnorm(x, mean(res), sd(res)), add=T)
acf(res, main="FAC dos res?duos", ylab="FAC", lag.max=0.25*n1)
pacf(res, main="FACP dos res?duos", ylab="FACP", lag.max=0.25*n1)


Box.test(res,lag = 1) #p-value = 0.8429>0.05, nao se rejeita H_0, os residuos sao
#nao correlacionados


# teste ? normalidade
shapiro.test(res) #p-value = 0.2346>0.05, n?o se rejeita a hipotese de normalidade


ks.test(res, "pnorm", mean=mean(res), sd=sd(res))
#p-value = 0.1658>0.05
# n?o se rejeita a hip?tese de normalidade

# teste ao valor m?dio
t.test(res, mu=0) #p-value = 0.1777>0.05
# n?o se rejeita a hip?tese de m?dia nula

# conclus?o: os res?duos apresentam um comportamento semelhante a um ru?do branco. 



####################### PREVIS?ES Para 2 anos ###########################
library(forecast)
library(lubridate)

#Modelo Escolhido: ARIMA(1,2,1)(0,1,1)[12]

# Validar o modelo, ignorando as ?ltimas 24 observa??es e comparando valores
# estimados e observados

#observados vs estimados (transforma??o)
est.dad = fitted.values(modelo)
res.dad = dados_est- est.dad
ts.plot(dados_est, main = "Dados Transformados com lambda=0.1")
lines(ts(est.dad, start=1949, frequency=12), col="red")

## observados vs estimados (original)
est = InvBoxCox(est.dad,lambda)
inver<- round(est, digits = 0)
res =  dados - est
ts.plot(dados, main = "Dados dos Passageiros")
lines(ts(inver, start=1949, frequency=12), col="red")


# Forecasting para 1959 e 1960
m1 = arima(dados_est, order=c(1,2,1), seasonal=list(order=c(0,1,1), period=12))
previsoes<- predict(m1, n.ahead = 24) #previs?es com dados transformados
inv_prev<-InvBoxCox(previsoes$pred,lambda)
inver_prev<- round(inv_prev, digits = 0) #previs?es com dados originais


#intervalos de previs?o - dados transformados
low = previsoes$pred - 1.96*previsoes$se
upper = previsoes$pred + 1.96*previsoes$se

#intervalos de previs?o - dados originais
low2 = round(InvBoxCox(low,lambda), digits = 0)
upper2 = round(InvBoxCox(upper,lambda), digits = 0)


# gr?fico de previs?o e estimados vs observados -  dados transformados
ts.plot(dados_est, main = "Dados Transformados", xlim=c(1949,1961))
lines(ts(est.dad, start=1949, frequency=12), col="red")
lines(ts(previsoes$pred, start=1959, frequency=12), col="blue")
lines(ts(low, start=1959, deltat=1/12), lty=3, col="blue")
lines(ts(upper, start=1959, deltat=1/12), lty=3, col="blue")

# gr?fico de previs?o e estimados vs observados -  dados originais
ts.plot(AirPassengers, main = "Totals of international airline passengers", ylab="Number of passengers", xlim=c(1949,1961))
lines(ts(inver, start=1949, frequency=12), col="red")
lines(ts(inver_prev, start=1959, frequency=12), col="blue")
lines(ts(low2, start=1959, deltat=1/12), lty=3, col="blue")
lines(ts(upper2, start=1959, deltat=1/12), lty=3, col="blue")
legend("topleft", legend = c("S?rie observada", "Estimativas", "Previs?es", "Intervalos de previs?o (95%)"), col = c("black", "red", "blue", "blue"), lty = c(1,1,1,2), bty="n")




####################### Utilizando a Fun??o Logaritmo ####################

######## Estabilizar a vari?ncia ############

ldados<-log(dados)
plot(ldados, ylab="dados") #vari?ncia estabilizada


n1 = length(ldados); n1 #120
par(mfrow=c(1,2))
acf(ldados, lag.max = 0.25*n1) # decaimento exponencial para zero - indica n?o estacionariedade
pacf(ldados, lag.max = 0.25*n1)


############# teste de estacionariedade (raiz unit?ria)

## teste ADF
# H0: Existe pelo menos uma raiz dentro do c?rculo unit?rio (a s?rie n?o ? estacion?ria)
# H1: N?o existem ra?zes dentro do c?rculo unit?rio (a s?rie ? estacion?ria)
## https://www.quora.com/How-do-I-interpret-the-results-in-an-augmented-Dickey-Fuller-test
## rejeita-se H0, ou seja, a s?rie ? estacion?ria, se ET < -1.95 (n?vel 5%)


par(mfrow=c(1,2));plot(ldados);acf(ldados)

## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
p = trunc(12 * (n1/100)^(1/4)); p #maior inteiro que o numero contem

testeADF = ur.df(ldados, lags=p, type="trend")
summary(testeADF)
#dado que -0.7646>tau3, nao podemos rejeitar a hipotese de que pi=0, devemos procurar aumentar o poder do teste.
#(ou seja, testar se a tendencia ? estatisticamente significativa (phi3)).
#como 2.2618<6.49, nao podemos rejeitar,logo podemos concluir que o termo da tend?ncia pode ser retirado para
#que o poder do teste fique maior.


testeADF = ur.df(ldados, lags=p, type="drift")
summary(testeADF)
#tt significativo
#-2.0552>tau2, n?o podemos rejeitar H_0
#Para verificar se podemos aumentar o poder do teste (phi1): 7.5192>4.63
# podemos rejeitar que alpha=0|pi=0, devemos inserir o termo drift da regress?o de teste.


#-----//------
#Como no teste anterior conclui-se que dever ser utilizado o termo drift, n?o ? necess?rio realizar este teste.
testeADF = ur.df(ldados, lags=p)
summary(testeADF)
#-----//------


## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
kpss = ur.kpss(ldados, type="tau")  # se tt significativo no teste ADF
#kpss = ur.kpss(ldados, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.0606<0.146
# ET < VC - n?o se rejeita a hip?tese nula de estacionariedade

## Quando o teste ADF d? n?o estacion?rio e o teste KPSS d? estacion?rio conclui-se que a s?rie ? n?o estacion?ria. 
#Conclus?o: A s?rie n?o ? estacion?ria.


############# ordem da diferencia??o d=? (estabilizar tend?ncia)

library(forecast)
ndiffs(ldados)   # d=1 #sugere quantas diferencia??es vao ter de ser realizadas
nsdiffs(ldados)    # D=1 #sugere as diferencia?oes da parte sazonal 

dif = arima(ldados, order=c(0,1,0))
layout(matrix(c(1,1,2,3), 2, byrow=T))
plot(dif$residuals)
acf(dif$residuals, main = "FAC(d=1)", lag.max = 0.25*n1)
pacf(dif$residuals, main = "FACP(d=1)", lag.max = 0.25*n1)


## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
p = trunc(12 * (n1/100)^(1/4)); p


testeADF = ur.df(dif$residuals, lags=p, type="trend")
summary(testeADF)
# tt significativo
#-2.9663>-3.43, logo n?o se rejeita H_0, a s?rie ? n?o estacion?ria
#5.0254<6.49, logo o termo da tend?ncia pode ser retirado


testeADF = ur.df(dif$residuals, lags=p, type="drift")
summary(testeADF)
#tt significativo
#-2.4923>tau2, n?o podemos rejeitar H_0
#Para verificar se podemos aumentar o poder do teste (phi1): 3.1071<4.63
# podemos rejeitar que alpha=0|pi=0, devemos retirar o termo drift da regress?o de teste.


testeADF = ur.df(dif$residuals, lags=p)
summary(testeADF)
#tt nao significativo
#-1.1178>-1.95, n?o podemos rejeitar H_0, a s?rie ? n?o estacion?ria


## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
#kpss = ur.kpss(dif$residuals, type="tau")  # se tt significativo no teste ADF
kpss = ur.kpss(dif$residuals, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.2495<0.463
#ET<VC --> a s?rie ? estacion?ria

#Quando o teste ADF d? n?o estacion?rio e o teste KPSS d? estacion?rio conclui-se que a s?rie ? n?o estacion?ria.
### Conclus?o: A s?rie ? n?o estacion?ria ap?s uma diferencia??o. 


#2? diferencia??o

dif2 = arima(ldados, order=c(0,2,0))
layout(matrix(c(1,1,2,3), 2, byrow=T))
plot(dif$residuals)
acf(dif$residuals, main = "FAC(d=1)", lag.max = 0.25*n1)
pacf(dif$residuals, main = "FACP(d=1)", lag.max = 0.25*n1)


## teste ADF (H0: n?o estacion?ria; rejeitar se ET < VC)
library(urca)
p = trunc(12 * (n1/100)^(1/4)); p


testeADF = ur.df(dif2$residuals, lags=p, type="trend")
summary(testeADF)
# tt n?o significativo
#-7.7162<-3.43, logo rejeita-se H_0, a s?rie ? estacion?ria
#29.8201>6.49, logo o termo da tend?ncia pode ser inserido na regressao de teste.

#----//-------
#Como no teste anterior conclui-se que dever ser utilizado o termo trend, n?o ? necess?rio realizar estes testes.
testeADF = ur.df(dif2$residuals, lags=p, type="drift")
summary(testeADF)

testeADF = ur.df(dif2$residuals, lags=p)
summary(testeADF)
#---//------

## teste KPSS (H0: estacion?ria; rejeitar se ET > VC)
#kpss = ur.kpss(dif$residuals, type="tau")  # se tt significativo no teste ADF
kpss = ur.kpss(dif2$residuals, type="mu", use.lag=p) # se tt n?o significativo no teste ADF
summary(kpss)
#0.0856<0.463
#ET<VC --> a s?rie ? estacion?ria

### Conclus?o: A s?rie ? estacion?ria ap?s a 2? diferencia??o. 


# definimos d=2
dif2 = dif2$residuals

############## sazonalidade ###################

### determinar s

# atrav?s do periodograma
periodogram=spectrum(as.vector(dados), plot=F)
imax=which.max(periodogram$spec)
periodo=1/periodogram$freq[imax]
periodo #12

# consideramos s=12


### determinar D, P e Q
auto.arima(dif2)
#Modelo sugerido: ARIMA(4,0,1)(0,1,1)[12] 

# Fazer P=1, D=Q=0. Se coeficiente AR pr?ximo de 1, ent?o D=1 


seas1 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(1,0,0), period = 12))
summary(seas1)
#sar1 pr?ximo de 1 por isso definimos D=1

seas2 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(1,1,0), period = 12))
summary(seas2)
BIC(seas2)
#AIC= -256.35, BIC= -251.0192

seas3 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(0,1,1), period = 12))
summary(seas3)
BIC(seas3)
#AIC= -268.84, BIC= -263.5096

seas4 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(1,1,1), period = 12))
summary(seas4)
BIC(seas4)
#AIC= -267.11, BIC= -259.1189

seas5 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(2,1,1), period = 12))
summary(seas5)
BIC(seas5)
#AIC= -266.02, BIC= -255.3625

seas6 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(1,1,2), period = 12))
summary(seas6)
BIC(seas6)
#AIC= -266.4, BIC= -255.742

### Modelo com menor AIC e menor BIC: P=0, D=1, Q=1
# os coeficientes s?o significativamente diferentes de 0?
seas3$coef[1] + c(-1,1) * qnorm(0.975) * sqrt(seas3$var.coef[1,1]) # = (-0.8766051; -0.4710325) -> sim
#coeficiente estatisticamente significativo



###################### determinar p e q

m0 = arima(ldados, order = c(0,2,0), seasonal = list(order = c(0,1,1), period = 12))
summary(m0)
BIC(m0)
#AIC= -268.84, BIC= -263.5096

m1 = arima(ldados, order = c(1,2,0), seasonal = list(order = c(0,1,1), period = 12))
summary(m1)
BIC(m1)
#AIC= -324.19, BIC= -316.1961

m2 = arima(ldados, order = c(0,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(m2)
BIC(m2)
#AIC= -361.61, BIC= -353.6216

m3 = arima(ldados, order = c(2,2,2), seasonal = list(order = c(0,1,1), period = 12))
summary(m3)
BIC(m3)
#AIC= -366.73, BIC= -350.7502


#"current model": ARIMA(2,2,2)(0,1,1)[12] com AIC= -366.73, BIC= -350.7502

#varia??es do "current model": 

m4 = arima(ldados, order = c(1,2,2), seasonal = list(order = c(0,1,1), period = 12))
summary(m4)
BIC(m4)
#AIC= -368.02, BIC= -354.6984

m5 = arima(ldados, order = c(1,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(m5)
BIC(m5)
#AIC= -369.79, BIC= -359.1361

m6 = arima(ldados, order = c(2,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(m6)
BIC(m6)
#AIC= -367.79, BIC= -354.4747

##Modelo Escolhido: ARIMA(1,2,1)(0,1,1)[12]
modelo = arima(ldados, order = c(1,2,1), seasonal = list(order = c(0,1,1), period = 12))
summary(modelo)

modelo$coef[1] + c(-1,1) * qnorm(0.975) * sqrt(modelo$var.coef[1,1]) #(-0.4878184, -0.1234954)
modelo$coef[2] + c(-1,1) * qnorm(0.975) * sqrt(modelo$var.coef[2,2]) #(-1.1143936, -0.8826693)
modelo$coef[3] + c(-1,1) * qnorm(0.975) * sqrt(modelo$var.coef[3,3]) #(-0.7142144, -0.3646833)
#coeficientes significativos (porque o zero n?o pertence ao intervalo)

## AVALIAR SE OS RES?DUOS APRESENTAM UM COMPORTAMENTO SEMELHANTE A UM RU?DO BRANCO 
res = modelo$residuals

layout(matrix(c(1,2,3,4),2,byrow=T))
plot(res, main="Representa??o gr?fica dos res?duos", ylab="")
hist(res, freq=F, main="Histograma dos res?duos", xlab="res?duos", ylab="frequ?ncia relativa")
curve(dnorm(x, mean(res), sd(res)), add=T)
acf(res, main="FAC dos res?duos", ylab="FAC", lag.max=0.25*n1)
pacf(res, main="FACP dos res?duos", ylab="FACP", lag.max=0.25*n1)


Box.test(res,lag = 1) #p-value = 0.8036>0.05, nao se rejeita H_0, os residuos sao
#nao correlacionados


# teste ? normalidade
shapiro.test(res) #p-value = 0.2386>0.05, n?o se rejeita a hipotese de normalidade


ks.test(res, "pnorm", mean=mean(res), sd=sd(res))
#p-value = 0.137>0.05
# n?o se rejeita a hip?tese de normalidade

# teste ao valor m?dio
t.test(res, mu=0) #p-value = 0.1772>0.05
# n?o se rejeita a hip?tese de m?dia nula

# conclus?o: os res?duos apresentam um comportamento semelhante a um ru?do branco. 



####################### PREVIS?ES Para 2 anos ###########################
library(forecast)
library(lubridate)

#Modelo Escolhido: ARIMA(1,2,1)(0,1,1)[12]

# Validar o modelo, ignorando as ?ltimas 24 observa??es e comparando valores
# estimados e observados

#observados vs estimados (transforma??o)
est.log = fitted.values(modelo)
res.log = ldados- est.log
ts.plot(ldados, main = "Logaritmo dos Dados")
lines(ts(est.log, start=1949, frequency=12), col="red")

## observados vs estimados (original)
est = exp(est.log)
res =  dados - est
ts.plot(dados, main = "Dados dos Passageiros")
lines(ts(est, start=1949, frequency=12), col="red")


# Forecasting para 1959 e 1960
m1 = arima(ldados, order=c(1,2,1), seasonal=list(order=c(0,1,1), period=12))
previsoes<- predict(m1, n.ahead = 24) #previs?es com dados transformados
prev<-exp(previsoes$pred)#previs?es com dados originais


#intervalos de previs?o - dados transformados
low = previsoes$pred - 1.96*previsoes$se
upper = previsoes$pred + 1.96*previsoes$se

#intervalos de previs?o - dados originais
low2 = exp(low)
upper2 = exp(upper)


# gr?fico de previs?o e estimados vs observados -  dados transformados
ts.plot(ldados, main = "Dados Logaritmizados", xlim=c(1949,1961))
lines(ts(est.log, start=1949, frequency=12), col="red")
lines(ts(previsoes$pred, start=1959, frequency=12), col="blue")
lines(ts(low, start=1959, deltat=1/12), lty=3, col="blue")
lines(ts(upper, start=1959, deltat=1/12), lty=3, col="blue")
legend("bottomright", legend = c("S?rie observada", "Estimativas", "Previs?es", "Intervalos de previs?o (95%)"), col = c("black", "red", "blue", "blue"), lty = c(1,1,1,2), bty="n", cex = 0.8)


# gr?fico de previs?o e estimados vs observados -  dados originais
ts.plot(AirPassengers, main = "Totals of international airline passengers", ylab="Number of passengers", xlim=c(1949,1961))
lines(ts(est, start=1949, frequency=12), col="red")
lines(ts(prev, start=1959, frequency=12), col="blue")
lines(ts(low2, start=1959, deltat=1/12), lty=3, col="blue")
lines(ts(upper2, start=1959, deltat=1/12), lty=3, col="blue")
legend("topleft", legend = c("S?rie observada", "Estimativas", "Previs?es", "Intervalos de previs?o (95%)"), col = c("black", "red", "blue", "blue"), lty = c(1,1,1,2), bty="n", cex = 0.8)

