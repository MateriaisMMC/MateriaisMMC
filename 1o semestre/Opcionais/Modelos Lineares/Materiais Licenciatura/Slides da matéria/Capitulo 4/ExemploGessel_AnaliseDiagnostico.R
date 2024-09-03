##########
# gessel #
##########
dados<-read.table("gessel.txt", head=T)

Y <- dados[,2]
X <- dados[,1]
fit <- lm(Y~X)
summary(fit)
plot(X, Y,cex=0.4)
for (i in 1:21) text(X[i], Y[i]+1.5, i, cex=0.65)
for (i in c(18,19)) text(X[i], Y[i]+1.5, i,col="blue", cex=0.65)
abline(fit)


# OUTLIER - observação 19
rstandard(fit)
rstudent(fit)  #ri

plot(fit$res)
#plot(fit$res, fit$fitted.values)


# ELEVADO LEVERAGE - observação 18
fitinf <- influence(fit)
fitinf$hat>2*2/21

hatvalues(fit) > 2*2/21

#NOTA: sum hii=(p+1)
sum(fitinf$hat)

# ou análise gráfica
plot(1:21,fitinf$hat,ylab="Leverages")
which.max(fitinf$hat)


# INFLUENTE - observações 18 e 19
# mede a influência que a observação i tem em \hat{Y}
abs(dffits(fit)) > 2*sqrt(2/19) 
# Outras funções
dfbetas(fit)[,1] > 2/sqrt(21)

# mede a influência que a observação i tem em \hat{beta}
cook <- cooks.distance(fit)
plot(1:21,cook,ylab="Observações influentes")
cook>4/21
p=1; n=21
abs(cook)>pf(0.5,p+1,n-p-1)

# ou análise gráfica
plot(1:21,dffits(fit),ylab="Observações influentes")





