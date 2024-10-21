#    R code for: Chapter 18 in:
#    Analysing Ecological Data. (2007). Zuur, Ieno and Smith. Springer, 680p.

###################################################
#                                                 #
#    ESTATÍSTICA ESPACIAL                         #
#                                                 #
#    CÓDIGO R DE APOIO AOS ACETATOS DEDICADOS AOS #
#    MODELOS PARA DADOS AGREGADOS POR ÁREA        #
###################################################

#rm(list=ls())

#you must define your working directory
#setwd("......")




#########
# SLIDE 2 
#########
library(spatstat)
?spatstat

# Distance between the 10 points given in slide 2
#     Table 18.2 of Zuur et al book
irreg_lattice <- read.table("CentPoint.txt", header = TRUE)
w <- as.owin(list(xrange = c(4.6, 21.1), yrange = c(84.5, 93.6)))

?as.ppp
point_pattern <- as.ppp(as.matrix(irreg_lattice), w)
plot(point_pattern)

? pairdist
dist_matrix <- pairdist(point_pattern)
dist_matrix <- as.dist(round(dist_matrix, 1), upper = T)
dist_matrix




#########
# SLIDE 7 
#########
library(tripack)
library(spatstat)
library(spdep)
library(sf)

plot_1_6 <- read.table("Plot_1_6.txt", header = TRUE)
plot_22_7 <- read.table("Plot_22_7.txt", header = TRUE)

# need to change the display window size to fit the axis to margins
w <- as.owin(list(xrange = c(3, 25), yrange = c(3, 25)))

par(mfrow = c(1, 2))
point_pattern.1_6 <- ppp(x = plot_1_6$X, y = plot_1_6$Y, 
                         window = w, marks = plot_1_6$height)
plot(point_pattern.1_6, maxsize = 0.5, main="1st Region", cex.main=0.8)

point_pattern.22_7 <- ppp(x = plot_22_7$X, y = plot_22_7$Y, 
                          window = w, marks = plot_22_7$height)
plot(point_pattern.22_7, maxsize = 0.5, main="2nd Region", cex.main=0.8)


par(mfrow = c(2, 2))
#A
plot(point_pattern.1_6, maxsize = 0.5, main="1st Region", cex.main=0.8)
axis(1, at = seq(5, 25, 5)); axis(2, at = seq(5, 25, 5))

#B 
plot(point_pattern.22_7, maxsize = 0.5, main="2nd Region", cex.main=0.8)
axis(1, at = seq(5, 25, 5)); axis(2, at = seq(5, 25, 5))

#C
?voronoi.mosaic
v <- voronoi.mosaic(plot_1_6$X, plot_1_6$Y)
plot(plot_1_6[, 1:2], pch = 20, main="1st Region", cex.main=0.8, 
     xlab = "", ylab = "", xlim = c(3, 25), ylim = c(3, 25))
plot(v, add = TRUE, do.points = F)

#D
v <- voronoi.mosaic(plot_22_7[, 1], plot_22_7[, 2])
plot(plot_22_7[, 1:2], pch = 20, main="2nd Region", cex.main=0.8, 
     xlab = "", ylab = "", xlim = c(3, 25), ylim = c(3, 25))
plot(v, add = TRUE, do.points = F)



#########
# SLIDE8 
#########
library(spdep)
?tri2nb
nb <- tri2nb(as.matrix(plot_1_6[, 1:2]));nb #Number of regions: 70 
?nb2listw. #Matriz de pesos
W <- nb2listw(nb, style = "W") # argumento style premite definir que tipo de matriz queremos
?moran.test
moran.test(plot_1_6$height, W, alternative = "two.sided")
-1/(70-1) #= Expectation(esperança) - formula no slide 6 
#Sao relacionados

###########
# EXERCICIO: Analisar se há correlação espacial entre as alturas das árvores na região 2.
#E os diametros sao relacionados?
###########

nb <- tri2nb(as.matrix(plot_22_7[, 1:2]));nb #Number of regions: 54 
W <- nb2listw(nb, style = "W") # argumento style premite definir que tipo de matriz queremos
moran.test(plot_22_7$height, W, alternative = "two.sided")
names(W)
W$weights


#ver para os diametros

#########
# SLIDE 9 
#########
par(mfrow = c(1, 2))

plot_1_6 <- read.table("Plot_1_6.txt", header = TRUE)
summary(dist(plot_1_6[,1:2]))

distance_band <- c(2.5, 5, 7.5, 10, 12.5, 15)
dist_ring_count <- length(distance_band) - 1
I <- data.frame(distance = 0, 
              z.score = 0, 
              Index = 0, 
              expectation = 0, 
              variance = 0, 
              p.value = 0)

library(spdep)
for(i in 1:dist_ring_count) {
  nb <- dnearneigh(as.matrix(plot_1_6[, 1:2]), distance_band[i], 
                                               distance_band[i + 1])
  W <- nb2listw(nb, style = "B")
  M <- moran.test(plot_1_6$height, W, alternative = "two.sided")
  I[i, 1] <- 0.5*(distance_band[i + 1] + distance_band[i])
  I[i, 2] <- M$statistic
  I[i, 3] <- M$estimate[1]
  I[i, 4] <- M$estimate[2]
  I[i, 5] <- M$estimate[3]
  I[i, 6] <- M$p.value
}
I[, c(1, 6)]
plot(I$distance, I$z.score, ylim = c( - 4, 4), 
     xlab = expression(paste("Distance ",d[k])), ylab = expression(paste("standardized  ",I^(k))), main = "1st Region")

lines(I$distance, I$z.score)
#    Expectation. see that I$expectation == - 1/(count of trees - 1)
abline(h = - 1/(nrow(plot_1_6) - 1))
abline(h = + 1.96, lty = 2)
abline(h = - 1.96, lty = 2)

plot_22_7 <- read.table("Plot_22_7.txt", header = TRUE)
distance_band <- c(2.5, 5, 7.5, 10, 12.5, 15)
dist_ring_count <- length(distance_band) - 1
I <- data.frame(distance = 0, 
              z.score = 0, 
              Index = 0, 
              expectation = 0, 
              variance = 0, 
              p.value = 0)
library(spdep)
for(i in 1:dist_ring_count) {
  nb <- dnearneigh(as.matrix(plot_22_7[, 1:2]), distance_band[i], 
                                                distance_band[i + 1])
  W <- nb2listw(nb, style = "B")
  M <- moran.test(plot_22_7$height, W, alternative = "two.sided")
  I[i, 1] <- 0.5*(distance_band[i + 1] + distance_band[i])
  I[i, 2] <- M$statistic
  I[i, 3] <- M$estimate[1]
  I[i, 4] <- M$estimate[2]
  I[i, 5] <- M$estimate[3]
  I[i, 6] <- M$p.value
}
I[, c(1, 6)]
plot(I$distance, I$z.score, ylim = c( - 4, 4),  
     xlab = expression(paste("Distance ",d[k])), ylab = expression(paste("standardized  ",I^(k))), 
     main = "2nd Region")
lines(I$distance, I$z.score)
#    Expectation. See that I$expectation ==  - 1/(count of trees - 1)
abline(h = - 1/(nrow(plot_22_7) - 1))
abline(h = + 1.96, lty = 2)
abline(h = - 1.96, lty = 2)



##########
# SLIDE 10 
##########
# Example of linear regression applied on tree height data 
plot_1_6 <- read.table("Plot_1_6.txt", header = TRUE)
model_LM <- lm(height ~ diameter, data = plot_1_6)
summary(model_LM)
AIC(model_LM)


#     Morans I test on the residuals of the fitted linear model
library(spdep)
?tri2nb
nb <- tri2nb(as.matrix(plot_1_6[, 1:2]))
W <- nb2listw(nb, style = "W")

?lm.morantest
model_LM.moran <- lm.morantest(model_LM, W, alternative = "greater", 
                               resfun = weighted.residuals)
model_LM.moran

#     Morans I
cat("Morans I", model_LM.moran$estimate[1], "\n")

#     p-value
cat("p-value", model_LM.moran$p.value, "\n")
#    this means that there is evidence of spatial 
#    auto - correlation in the residuals





##########
# SLIDE 13 
##########
# Example of a SAR model for tree height data 
plot_1_6 <- read.table("Plot_1_6.txt", header = TRUE)

library(spdep)
nb <- tri2nb(as.matrix(plot_1_6[, 1:2]))
W <- nb2listw(nb, style = "W")

#library(expm)
library(spatialreg)
?lagsarlm
model_SAR <- lagsarlm(height ~ diameter, data = plot_1_6, W, 
                      method = "eigen", quiet = TRUE)
summary(model_SAR)
names(model_SAR)

#     residual standard error
sqrt(model_SAR$SSE/nrow(plot_1_6))

#     To examine auto - correlation of residuals:
moran.test(model_SAR$residuals, W, alternative = "two.sided") #p-value = 0.2063
# Alternativa:
summary(model_SAR)$Wald1



##########
# SLIDE 14 
##########
# Example of a SMA model for a tree height data 
plot_1_6 <- read.table("Plot_1_6.txt", header = TRUE)

library(spdep)
nb <- tri2nb(as.matrix(plot_1_6[, 1:2]))
W <- nb2listw(nb, style = "W")

library(spatialreg)
?errorsarlm
model_SMA <- errorsarlm(height ~ diameter, data = plot_1_6, W, 
                        method = "eigen", quiet = TRUE)
summary(model_SMA)

#     residual standard error
sqrt(model_SMA$SSE/nrow(plot_1_6))

#     To examine auto - correlation of residuals:
moran.test(model_SMA$residuals, W, alternative = "two.sided") #p-value = 0.9131
summary(model_SMA)$Wald1





##########
# SLIDE 15 
##########
# linear regression 

plot_1_6 <- read.table("Plot_1_6.txt", header = TRUE)
species_LM <- lm(height ~ diameter + as.factor(code_spec), 
                 data = plot_1_6)
summary(species_LM)
AIC(species_LM)

#     Morans I test on the residuals of the fitted linear model
library(spdep)
nb <- tri2nb(as.matrix(plot_1_6[, 1:2]))
W <- nb2listw(nb, style = "W")
species_LM.moran <- lm.morantest(species_LM, W, alternative = "greater",
                                 resfun = weighted.residuals)
species_LM.moran

#     Morans I
cat("Moran's I", species_LM.moran$estimate[1], "\n")

#     p-value
cat("p-value", species_LM.moran$p.value, "\n")
#    this means that there is no evidence of spatial 
#    auto - correlation in the residuals






