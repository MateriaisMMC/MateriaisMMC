#The random walk (RW) model is also a basic time series model. 
#It is the cumulative sum (or integration) of a mean zero white noise (WN) series, 
#such that the first difference series of a RW is a WN series. 
#Note for reference that the RW model is an ARIMA(0, 1, 0) model, in which the 
#middle entry of 1 indicates that the model's order of integration is 1.
#https://campus.datacamp.com/courses/time-series-analysis-in-r/predicting-the-future?ex=11

#Passeio aleatório
#https://financetrain.com/simulate-random-walk-rw-in-r
RW_drift <- arima.sim(model= list(order = c(0, 1, 0)), n=100, mean=0.5,sd=1)
plot.ts(RW_drift, main="Random Walk with Drift")

#ou
e <- rnorm(100,0,1)
y1 <- cumsum(e)
RW_drift <- 0.5 * 1:100 + cumsum(e)
plot.ts(RW_drift, main="Random Walk with Drift")

#Passeio aleatório
e <- rnorm(100,0,1)
y1 <- cumsum(e)
plot.ts(y1, main="Random Walk")

#Ruído branco
#https://financetrain.com/simulate-white-noise-wn-in-r
WN <- arima.sim(model = list(order = c(0, 0, 0)), n = 100, mean=50, sd=10)
plot.ts(WN,col=1, main="White Noise Series (mean=50, sd=10)")

#ou
#https://otexts.com/fpp2/wn.html

WN <- ts(rbinom(100,50,0.5))
plot.ts(WN,col=1, main="White Noise Series (n=50, p=0.5)")

WN <- ts(rnorm(100,0,4))
plot.ts(WN,col=1, main="White Noise Series (me=0 e var=4)")
#Para criar um ruído branco não gaussiano, apenas seja suficiente
#alterar o rnorm() para outra distribuição, p.e., rbinom(), rexp(), runif()
#1. Modelo estacionario em media mas nao em variancia (mistura de 2 distribuicoes
# gaussianas)
#n=dimensão total da amostra simulada
#t0=dimensão da primeira distribuicao
#par(mfrow=c(1,2))

n=250
t0=125
sample1 <- c(rnorm(t0,mean=0,sd=1),rnorm(n-t0,mean=0,sd=5))
plot.ts(sample1, xlab="tempo",ylab="")

#2. Tendencia linear e Sazonalidade (modelo multiplicativo): 
# não estacionário em variância

t=250
e=rnorm(t, 0, 1)
sample2=rep(NA,t)
for (i in 1:t){
  sample2[i] <- (2+1/10*i)*abs(3*cos((2*pi*i)/25))+e[i]
}
sample2
plot.ts(sample2, xlab="tempo",ylab="")

#3. Tendência linear e Sazonalidade (modelo multiplicativo misto)
t=250
e=rnorm(t, 0, 1)
sample3=rep(NA,t)
for (i in 1:t){
  sample3[i] <- (2+i/10)+(2+i/10)*(3*cos((2*pi*i)/25))+e[i]
}

#sample3= (2+c(1:250)/10)+(2+c(1:250)/10)*(3*cos((2*pi*c(1:250))/25))+e
#sample3
plot.ts(sample3, xlab="tempo",ylab="")


#4. Tendência linear e Sazonalidade (modelo aditivo)
t=250
sample4 <- (2+c(1:t)/10)+(3*cos((2*pi*c(1:t))/25))+rnorm(t, 0, 1)
plot.ts(sample4, xlab="tempo",ylab="")




