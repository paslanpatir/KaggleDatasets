#HOME = "C:\\Users\\paslanpatir\\Documents\\GitHub\\Soostone\\"
HOME = "C:\\Users\\pelin.yurdadon\\Desktop\\Soostone\\"
setwd(HOME)

options(scipen=999)
options(warnings = -1)

library(data.table)
library(tidyverse)

library(ggplot2)
library(gridExtra)
library(corrplot)
library(treemapify)

library(lubridate)
library(stringr); library(stringi)

library(skimr)
library(zoo)

library(Hmisc)

library(mice) ## imputation
library(VIM)

library(e1071) # svm
library(glmnet) # lasso
library(xgboost) #xgboost
#library(caret) # for general ml applications

library(cluster)    # clustering algorithms
library(factoextra) # clustering algorithms & visualization

# define a function to make plain the characters
to.plain <- function(s) {
  
  s= str_trim(str_to_lower(s, locale = "en"), side = c("both"))
  s = gsub("\\s","",s)
   
  chars = "[\\/\\(\\)\\-\\+\\&\\*]"
  
  s= str_replace_all(s, chars, "")
  return(s)
}

# change from "-" to NA 
make_null = function(s,selected_char){
    return(ifelse(s == "" | str_detect(s,selected_char),NA,s))
}

make_null_0 = function(s){
    return(ifelse(s == 0,NA,s))
}

fill_missing = function(x,method = ""){
    if(method == "mean"){
        y = mean(x,na.rm = TRUE)
        x[is.na(x)] = y
        return(x)
    }else if(method == "freq"){ # freq
        y= x[!is.na(x)]
        y = names(which.max(table(y)))
        x[is.na(x)] = y
        return(x)
    }else {
        return(x)
    }
}

## encode some columns
encode_numeric <- function(x, order = unique(x)) {
  x <- as.numeric(factor(x, levels = order, exclude = NULL))
  return(x)
}

encode_grouping = function(x,Q = 10,P  = NA,name_for_other = "other"){
    x_dt = data.table(t(t(table(x))))
    if(is.na(P)){
      x_dt = x_dt[order(-N)][1:(Q-1)]
  
      survivors = x_dt$x
      
    }else{
        sm = summary(x_dt$N)
        survivors = x_dt[N > sm[[P + 1]]]$x
    }
  x[!x %in% survivors] = name_for_other
  return(x)  
}

get_scale_params = function(data, feature_columns){
  x = data[,.SD,.SDcols = feature_columns]
  x_scaled = scale(x,center= TRUE,scale = TRUE)
  x = as.matrix(x_scaled) 
  
  Scale_Parameters = data.table("features" = attr(x_scaled,"dimnames")[[2]],
                                "means" = attr(x_scaled,"scaled:center"),
                                "sd"    = attr(x_scaled,"scaled:scale"))
  
  return(Scale_Parameters)
}


scale_external = function(dt,ScaleParams){
  for(i in ScaleParams$features){
    mean = ScaleParams[features == i]$means
    sd   = ScaleParams[features == i]$sd
    sd = ifelse(sd == 0,0.000001,sd)
    
    dt[, temp:= .SD, .SDcols = i]
    dt[, temp:= (temp - mean)/ sd]
    
    dt[,(i) := temp]
    dt[, temp := NULL]
  }
  return(dt)
}

calc_rmse= function(x,y){ return(sqrt(mean((x-y)^2)))}

normalize_between_01 = function(x){
max = max(x)
min = min(x)

x = (x - min)/(max-min)
return(x)
}

## boxplots of different features wrt a specific column 
draw_boxplot = function(dt,id_col = NULL, selected_cols){
    dt_molten = dt[,.SD,.SDcols = c(id_col,selected_cols)] %>% melt.data.table(id.vars = id_col)

    ggplot(data = dt_molten,aes_string(x = quo_name(id_col),fill = quo_name(id_col)))+ 
    geom_boxplot(aes(y = value)) +
    facet_wrap(~ variable, scales = "free") + 
    theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))
}

draw_barplot = function(dt,selected_cols,group_number,bin_number = NA,ncol){
    options(scipen=999)
    
    num_cols = dt[,.SD,.SDcols = selected_cols] %>% purrr::keep(is.numeric) %>% colnames()
    num_data = dt[,.SD,.SDcols = num_cols]
    if(is.na(bin_number)){
    num_data[, (num_cols):=  lapply(.SD, Hmisc::cut2, g = group_number),.SDcols = num_cols ]
        }else{
    num_data[, (num_cols):=  lapply(.SD, cut, breaks = bin_number,dig.lab=10),.SDcols = num_cols ]
        }
       
    new_data = cbind(dt[,.SD,.SDcols = c(setdiff(selected_cols,num_cols))],num_data)
    new_data_molten = new_data %>% tidyr::gather() 
    
    
    ggplot(data = new_data_molten,aes(x = value, fill = key))+ 
      facet_wrap(~ key, scales = "free",ncol = ncol) + 
      geom_bar() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))
}

draw_corplot = function(data){
    data %>% cor() %>%
    corrplot::corrplot.mixed(upper = "ellipse",
                         lower = "number",
                         tl.pos = "lt",
                         number.cex = .5,
                         lower.col = "black",
                         tl.cex = 0.7)
}

tend_outliers_del = function(dt,focus_col, sigma = 3){

    temp = dt[[focus_col]]
    m  = mean(temp)
    sd = sd(temp)
    
    lb = m - sigma*sd
    ub = m + sigma*sd
    
    temp = temp[temp < ub]
    temp = temp[temp > lb]
    
    m  = mean(temp)
    sd = sd(temp)
    lb = m - sigma*sd
    ub = m + sigma*sd
    
    dt = dt[dt[[focus_col]]<ub]
    dt = dt[dt[[focus_col]]>lb]
  return(dt)
}

tend_outliers_keep = function(x, sigma = 3){
  if(is.numeric(x) || is.integer(x)){
    temp = copy(x) 
    m  = mean(temp)
    sd = sd(temp)
    
    lb = m - sigma*sd
    ub = m + sigma*sd
    
    temp = temp[temp < ub]
    temp = temp[temp > lb]
    
    m  = mean(temp)
    sd = sd(temp)
    lb = m - sigma*sd
    ub = m + sigma*sd
    
    temp = copy(x)
    temp[temp > ub] = ub 
    temp[temp < lb] = lb
    return(temp)
  }
  return(x)
}

tend_outliers_keep_IQR = function(x, IQR = 2){
  if(is.numeric(x) || is.integer(x)){
    temp = copy(x) 
    q = quantile(temp)
    third = q[[4]]
    max_limit= third*IQR

    temp[temp> max_limit] = max_limit
    
    return(temp)
  }
  return(x)
}

model_xgboost= function(feature_list,target,chunk_no = 10){
    dt_model = copy(dt[,.SD,.SDcols = c("idx",target,feature_list)])
    
    chunk_no = 10
set.seed(0)
folds <- cut(seq(1,nrow(dt_model)),breaks=chunk_no,labels=FALSE)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

for(i in 1:chunk_no){
  #Segment your data by fold using the which() function 

  testIndexes <- which(folds==i,arr.ind=TRUE)
  testData    <- dt_model[testIndexes, ]
  trainData   <- dt_model[-testIndexes, ]
  
   y_train        = trainData[[target]]
   y_test         = testData[[target]]
    
    Scale_Parameters = get_scale_params(trainData, feature_list)
    x_train = scale(trainData[,.SD,.SDcols = feature_list])
    
    x_test = testData[,.SD,.SDcols = feature_list]
    scale_external(x_test,Scale_Parameters)
    
  d_train= xgb.DMatrix(data = as.matrix(x_train), label = y_train)
  d_test = xgb.DMatrix(data = as.matrix(x_test), label = y_test)
  
  set.seed(i)
  xg.model = xgb.train( data = d_train, 
                        nrounds = 20,
                        early_stopping_rounds = 3,
                        params = params, 
                        watchlist = list(train = d_train, test = d_test))
  
  if(str_detect(target,"log") == TRUE){
      xg.pred  = exp(predict(xg.model, d_test))
      actual = exp(y_test)
      
      xg.fitted = exp(predict(xg.model, d_train))
  }else{
      xg.pred  = predict(xg.model, d_test)
      actual = y_test
      
      xg.fitted = exp(predict(xg.model, d_train))
  }
    
   imp = data.table(xgb.importance( feature_names = colnames(x_train), model = xg.model))
   imp_table = rbind(imp_table,data.table(chunk = i, imp))  
    
    
  #Check performance
  sub_pred_table = testData[,.(idx, actual = actual, pred = xg.pred, chunk = i)]
  sub_fitted_table = trainData[,.(idx, fitted = xg.fitted, chunk = i )]
  
  pred_table = rbind(pred_table,sub_pred_table )
  fitted_table = rbind(fitted_table,sub_fitted_table )
 
}   

imp_table_2= dcast(imp_table, Feature ~ chunk, value.var = "Gain")
imp_table_2 = imp_table_2[order(-`5`)]
    
    return(list(pred_table,imp_table_2))
}

model_xgboost_partial= function(feature_list,target,chunk_no = 5){
    borough_list = unique(dt$borough)
    b_class_list = unique(dt$b_class_group)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

for(b in borough_list){
    for(c in b_class_list){
         dt_model_sub = copy(dt[ borough == b & b_class_group == c
                                     ,.SD
                                     ,.SDcols = c("idx","borough","b_class_group",target,feature_list)])
        chunk_no = 5
        set.seed(0)
        folds <- cut(seq(1,nrow(dt_model_sub)),breaks=chunk_no,labels=FALSE)
        
    # some columns might include NA values for some group of data
        incomplete_cols = colnames(dt_model_sub)[colSums(is.na(dt_model_sub)) !=0]
        feature_list= setdiff(feature_list, incomplete_cols)
        dt_model_sub = dt_model_sub[,(incomplete_cols):= NULL]
        rm(incomplete_cols)
        
        
        for(i in 1:chunk_no){
            testIndexes <- which(folds==i,arr.ind=TRUE)
            testData    <- dt_model_sub[testIndexes, ]
            trainData   <- dt_model_sub[-testIndexes, ]

            y_train        = trainData[[target]]
            y_test         = testData[[target]]
    
            Scale_Parameters = get_scale_params(trainData, feature_list)
            x_train = scale(trainData[,.SD,.SDcols = feature_list])
            
            x_test = testData[,.SD,.SDcols = feature_list]
            scale_external(x_test,Scale_Parameters)
    
            d_train= xgb.DMatrix(data = as.matrix(x_train), label = y_train)
            d_test = xgb.DMatrix(data = as.matrix(x_test), label = y_test)
  
            set.seed(i)
            xg.model = xgb.train( data = d_train, 
                                  nrounds = 20,
                                  early_stopping_rounds = 3,
                                  params = params, 
                                  watchlist = list(train = d_train, test = d_test))
            
            if(str_detect(target,"log") == TRUE){
                xg.pred  = exp(predict(xg.model, d_test))
                actual = exp(y_test)
                
                xg.fitted = exp(predict(xg.model, d_train))
            }else{
                xg.pred  = predict(xg.model, d_test)
                actual = y_test
                
                xg.fitted = exp(predict(xg.model, d_train))
            }
    
            imp = data.table(xgb.importance( feature_names = colnames(x_train), model = xg.model))
            imp_table = rbind(imp_table,data.table(borough = b, b_class_group = c,chunk = i, imp))  
    
    
             #Check performance
             sub_pred_table = testData[,.(idx, actual = actual, pred = xg.pred, chunk = i,borough = b, b_class_group = c)]
             sub_fitted_table = trainData[,.(idx, fitted = xg.fitted, chunk = i ,borough = b, b_class_group = c)]
             
             pred_table = rbind(pred_table,sub_pred_table )
             fitted_table = rbind(fitted_table,sub_fitted_table )
        }
    }
}
    
    imp_table_2 = imp_table[, .(avg_gain = mean(Gain)),.(borough,b_class_group,Feature)]
    
return(list(pred_table,imp_table_2))    
}

model_xgboost_partial_wo = function(feature_list,train_target,test_target,chunk_no = 5){
borough_list = unique(dt$borough)
b_class_list = unique(dt$b_class_group)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

for(b in borough_list){
    for(c in b_class_list){
        feature_list_used = copy(feature_list) 
        dt_model_sub = copy(dt[ borough == b & b_class_group == c
                                     ,.SD
                                     ,.SDcols = c("idx","borough","b_class_group",train_target,test_target,feature_list_used)])
        chunk_no = 5
        set.seed(0)
        folds <- cut(seq(1,nrow(dt_model_sub)),breaks=chunk_no,labels=FALSE)
        

        incomplete_cols = colnames(dt_model_sub)[colSums(is.na(dt_model_sub)) !=0]
        feature_list_used= setdiff(feature_list_used, incomplete_cols)
        dt_model_sub = dt_model_sub[,(incomplete_cols):= NULL]
        rm(incomplete_cols)
        
        
        for(i in 1:chunk_no){
            testIndexes <- which(folds==i,arr.ind=TRUE)
            testData    <- dt_model_sub[testIndexes, ]
            trainData   <- dt_model_sub[-testIndexes, ]

            y_train        = trainData[[train_target]]
            y_test         = testData[[test_target]]
    
            Scale_Parameters = get_scale_params(trainData, feature_list_used)
            x_train = scale(trainData[,.SD,.SDcols = feature_list_used])
            
            x_test = testData[,.SD,.SDcols = feature_list_used]
            scale_external(x_test,Scale_Parameters)
    
            d_train= xgb.DMatrix(data = as.matrix(x_train), label = y_train)
            d_test = xgb.DMatrix(data = as.matrix(x_test), label = y_test)
  
            set.seed(i)
            xg.model = xgb.train( data = d_train, 
                                  nrounds = 20,
                                  early_stopping_rounds = 3,
                                  params = params, 
                                  watchlist = list(train = d_train, test = d_test))
            
            if(str_detect(train_target,"log") == TRUE){
                xg.pred  = exp(predict(xg.model, d_test))
                actual = exp(y_test)
                
                xg.fitted = exp(predict(xg.model, d_train))
            }else{
                xg.pred  = predict(xg.model, d_test)
                actual = y_test
                
                xg.fitted = exp(predict(xg.model, d_train))
            }
    
            imp = data.table(xgb.importance( feature_names = colnames(x_train), model = xg.model))
            imp_table = rbind(imp_table,data.table(borough = b, b_class_group = c,chunk = i, imp))  
    
    
             #Check performance
             sub_pred_table = testData[,.(idx, actual = actual, pred = xg.pred, chunk = i,borough = b, b_class_group = c)]
             sub_fitted_table = trainData[,.(idx, fitted = xg.fitted, chunk = i ,borough = b, b_class_group = c)]
             
             pred_table = rbind(pred_table,sub_pred_table )
             fitted_table = rbind(fitted_table,sub_fitted_table )
        }
    }
}
    imp_table_2 = imp_table[, .(avg_gain = mean(Gain)),.(borough,b_class_group,Feature)]
    return(list(pred_table,imp_table_2))   
    }

dt = fread("nyc-rolling-sales.csv")

colnames(dt)
t(head(dt))

#skim(dt)

#dt %>% keep(is.character) %>% lapply(unique)

# https://www.kaggle.com/new-york-city/nyc-property-sales --> 'Datasets' says that:
# The combination of borough, block, and lot forms a unique key for property in New York City. Commonly called a BBL
dt[,bbl := paste(BOROUGH,BLOCK,LOT,sep="-")]

dt[,.N,.(bbl)][ N > 1][order(-N)]%>% head()
t(dt[bbl == '1-373-40'])
t(dt[bbl == '1-1006-1302'])

dt[,.N,.(V1,BOROUGH)][ N > 1]

# get rid of complete-Null column
dt[,`EASE-MENT` := NULL]

# change colnames for easy coding
cols = to.plain(colnames(dt))
colnames(dt) = cols

## make null -,_, or 0 for square feet columns
cols = setdiff(colnames(dt),"saledate")
dt[,(cols):= lapply(.SD, make_null, selected_char="-"), .SDcols = cols]
dt[,(cols):= lapply(.SD, make_null, selected_char="_"), .SDcols = cols]

sq_ft_cols = c("landsquarefeet","grosssquarefeet")
dt[,(sq_ft_cols):= lapply(.SD, make_null_0), .SDcols = sq_ft_cols]

# make character columns plain
character_cols = dt %>% keep(is.character) %>% colnames()
dt[,(character_cols):= lapply(.SD, to.plain), .SDcols = character_cols]

#  make numeric the columns below
numeric_cols = c("saleprice","grosssquarefeet","landsquarefeet")
dt[,(numeric_cols):= lapply(.SD, as.numeric), .SDcols = numeric_cols]

# define an id column 
dt[,idx := .GRP, .(v1,borough)]

 #dt[,easement := NULL]
dt[,bbl := paste(borough,block,lot,sep="-")]

colnames(dt)

dt[,b_class_cat := as.numeric(substr(buildingclasscategory,1,2))]

dt[,b_class_present := substr(buildingclassatpresent,1,1)]
dt[,b_class_past := substr(buildingclassattimeofsale,1,1)]
#dt[,b_style := substr(buildingclassattimeofsale,2,2)]


# by using the info on https://www1.nyc.gov/site/finance/taxes/property-determining-your-assessed-value.page
dt[,taxclass_present := as.numeric(substr(taxclassatpresent,1,1))]
dt[,taxclass_present_level := ifelse(nchar(taxclassatpresent) < 2,NA,substr(taxclassatpresent,2,2))]

dt[,taxclass_past := as.numeric(substr(taxclassattimeofsale,1,1))] # includes ony integer
#dt[,taxclass_past_level := ifelse(nchar(taxclassattimeofsale) < 2,NA,substr(taxclassattimeofsale,2,2))] ALL NA

t(head(dt))

skim(dt)

selected_cols = c("borough","zipcode","totalunits","commercialunits","residentialunits","yearbuilt","taxclass_past") 

options(repr.plot.width = 5, repr.plot.height = 5, repr.plot.res = 200)
draw_corplot(dt[,.SD,.SDcols = selected_cols])

options(repr.plot.width = 10, repr.plot.height = 3, repr.plot.res = 200)
r1 = ggplot(data = dt,aes(x = log(residentialunits), fill = "orange"))+ 
  geom_density() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))
c1= ggplot(data = dt,aes(x = log(commercialunits), fill = "orange"))+ 
  geom_density() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

grid.arrange(r1,c1,ncol = 2)

selected_cols = c("borough","yearbuilt","taxclass_past","taxclass_present","commercialunits") 
dt_c = copy(dt[,.SD,.SDcols = selected_cols]) 
dt_c = dt_c[complete.cases(dt_c)] # 738 records are deleted due to taxclass_present

options(repr.plot.width = 5, repr.plot.height = 5, repr.plot.res = 200)
draw_corplot(dt_c)


nrow(dt[taxclass_present != taxclass_past])
# only 46 records

selected_cols = c("borough","taxclass_present",'landsquarefeet','grosssquarefeet','totalunits',"commercialunits") 
dt_c = copy(dt[,.SD,.SDcols = selected_cols]) 
dt_c = dt_c[complete.cases(dt_c)] # 27970 records are deleted

options(repr.plot.width = 5, repr.plot.height = 5, repr.plot.res = 200)
draw_corplot(dt_c) 

#remove columns with NA values over 60% 
s = skim(dt)
dt_complete = data.table(variable = s$skim_variable,complete_rate = s$complete_rate)
selected_cols = dt_complete[complete_rate > 0.6]$variable

dt_c = copy(dt[,.SD,.SDcols = selected_cols])
dt_c = copy(dt_c[complete.cases(dt_c)]) # 53330 records are deleted 63% is deleted

options(repr.plot.width = 10, repr.plot.height = 10, repr.plot.res = 200)
numeric_cols = dt_c %>% keep(is.numeric) %>% colnames()
draw_corplot(dt_c[,.SD,.SDcols = numeric_cols])

table(dt[saleprice < 5000]$saleprice)

pre = nrow(dt)
dt= dt[!is.na(saleprice)]
dt= dt[saleprice != 0]
dt= dt[saleprice >200]
now = nrow(dt)

# percentage eliminated
100*(pre-now)/pre

min_yearbuilt = min(dt[yearbuilt>1111]$yearbuilt)
dt[yearbuilt <=1111, yearbuilt := min_yearbuilt]

table(dt$yearbuilt)

# Lets see if building class changes frequently
dt[, b_class_ischanged := ifelse(b_class_present != b_class_past,1,0)]
table(dt$b_class_ischanged)
# appearently, no, then lets eliminate one of the column

dt = dt[b_class_ischanged == 0]
dt[,c("b_class_ischanged","b_class_past") := NULL]

skim(dt)

dt[,c("taxclass_present_level","taxclass_past") := NULL]
dt = dt[!is.na(taxclass_present)] #593 records are eliminated
nrow(dt)

colSums(is.na(dt))
options(repr.plot.width = 5, repr.plot.height = 2, repr.plot.res = 200)
mice_plot <- aggr(dt, col=c('navyblue','yellow'),
                    numbers=TRUE, sortVars=TRUE,
                    labels=names(dt), cex.axis=.7,
                    gap=3, ylab=c("Missing data","Pattern"))
mice_plot


#nothing can be drawn from apartmentnumber, so we can delete it peacefully.
dt[,.N,.(apartmentnumber)][order(-N)] %>% head(5)

dt[,c("apartmentnumber") := NULL]

s = skim(dt)
dt_complete = data.table(variable = s$skim_variable,complete_rate = s$complete_rate)[complete_rate < 1]
dt_complete[order(complete_rate)]

b_class_freq = dt[,.N,.(b_class_present,b_class_cat)]
b_class_freq[, perc  := round(N / sum(N),2)]
b_class_freq[order(b_class_present)]
b_class_freq[order(b_class_present)][ perc > 0.05]

dt_tree = dt[,.(M = mean(saleprice, na.rm = TRUE), N = .N) ,.(buildingclasscategory)]

options(repr.plot.width = 5, repr.plot.height = 3, repr.plot.res = 200)
ggplot(dt_tree
       , aes(area = M, fill = N, label = buildingclasscategory)) +
  geom_treemap() +
  geom_treemap_text(colour = "white", place = "topleft", reflow = T)


#dt[,saleprice_group := Hmisc::cut2(saleprice,g = 10)]
#
#options(repr.plot.width = 12, repr.plot.height = 8, repr.plot.res = 200)
#ggplot(data = dt, aes(y = saleprice, x = as.factor(b_class_past), fill =as.factor(b_class_past))) + 
#    geom_boxplot() +
#    facet_wrap(~ saleprice_group,scales = "free", ncol = 2)
#
### b_class_cat'ı b_class_present ile doldurabiliriz.


b_groups = dt[,.N,.(b_class_present)][order(-N)]
b_groups[, perc := N/sum(N)][order(-perc)] 

dt[, b_class_group := encode_grouping(b_class_present, Q = 6,name_for_other = "other")]
dt[,.N,.(b_class_group)]

address_focus = dt$address
address_focus[str_detect(address_focus, "street")] = "street"
address_focus[str_detect(address_focus, "avenue")] = "avenue"
address_focus[str_detect(address_focus, "square")] = "square"
address_focus[str_detect(address_focus, "highway")] = "highway"
address_focus[str_detect(address_focus, "boulevard")] = "boulevard"
address_focus[str_detect(address_focus, "centralpark")] = "centralpark"
address_focus[str_detect(address_focus, "broadway")] = "broaadway"
address_focus[str_detect(address_focus, "road")] = "road"
address_focus[!address_focus %in% c("street","avenue","square","highway","boulevard","centralpark","broaadway","road")] = "other"
table(address_focus)

## lets try to simplify the address column
address_focus = dt$address
address_focus[str_detect(address_focus, "street")] = "street"
address_focus[str_detect(address_focus, "avenue")] = "avenue"
address_focus[!address_focus %in% c("street","avenue")] = "other"
table(address_focus)
dt$address = address_focus

selected_cols = c("saleprice","totalunits","commercialunits")

options(repr.plot.width = 8, repr.plot.height = 3, repr.plot.res = 200)
draw_boxplot(dt[saleprice < 2000000 & totalunits< 10 & commercialunits < 2],id_col = "address", selected_cols)

dt_tree = dt[saleprice < 10000000,.(N = .N, M = mean(saleprice,na.rm = TRUE)),.(borough,neighborhood)]

options(repr.plot.width = 10, repr.plot.height = 5, repr.plot.res = 200)
ggplot(dt_tree
       , aes(area = N, fill = M, label = neighborhood,
                subgroup = borough)) +
  geom_treemap() +
  geom_treemap_subgroup_border() +
  geom_treemap_subgroup_text(place = "centre", grow = T, alpha = 0.5, colour =
                             "black", fontface = "italic", min.size = 0) +
  geom_treemap_text(colour = "white", place = "topleft", reflow = T)

dt_tree = dt[saleprice < 10000000,.(N = .N, M = mean(saleprice,na.rm = TRUE)),.(borough,neighborhood)]

for(i in c(1:5)){
g = ggplot(dt_tree[borough == i]
           , aes(area = N, fill = M, label = neighborhood,subgroup = borough)) +
  geom_treemap() +
  geom_treemap_subgroup_border() +
  geom_treemap_subgroup_text(place = "centre", grow = T, alpha = 0.5, colour =
                             "black", fontface = "italic", min.size = 0) +
  geom_treemap_text(colour = "white", place = "topleft", reflow = T) 
    
    assign(paste0("g_",i),g)
    }

options(repr.plot.width = 15, repr.plot.height = 5, repr.plot.res = 200)
gridExtra::grid.arrange(g_1,g_2,g_3,g_4,g_5, nrow = 2)

loc_cols = c('borough','block','lot',"zipcode")

options(repr.plot.width = 10, repr.plot.height = 3, repr.plot.res = 200)
draw_barplot(dt,loc_cols,bin_number = 10,ncol = 4)
draw_barplot(dt,loc_cols,group_number = 10,ncol = 4)

selected_cols = c('residentialunits','commercialunits','totalunits','landsquarefeet','grosssquarefeet','yearbuilt')

options(repr.plot.width = 10, repr.plot.height = 3, repr.plot.res = 200)
draw_barplot(dt,selected_cols,bin_number = 10,ncol = 6)
draw_barplot(dt,selected_cols,group_number = 10,ncol = 6)

dt_c = copy(dt[   ,.(residential_group = Hmisc::cut2(residentialunits, g = 10),
                  commerical_group = Hmisc::cut2(commercialunits, g = 10),
                  totalunit_group = Hmisc::cut2(totalunits, g = 10),
                  landsquarefeet_group = Hmisc::cut2(landsquarefeet, g = 10),
                  grosssquarefeet_group = Hmisc::cut2(grosssquarefeet, g = 10),
                     grosssquarefeet_log_group = Hmisc::cut2(log(grosssquarefeet), g = 10),
                     grosssquarefeet_log = log(grosssquarefeet),
                  yearbuilt_group = Hmisc::cut2(yearbuilt, g = 10),
                  saleprice,
                  saleprice_log = log(saleprice),
                saleprice_sqrt = sqrt(saleprice),
                      totalunits,
                      commercialunits,
                      yearbuilt,
                      grosssquarefeet,
                      zipcode,
                  address,
                  borough = as.factor(borough),
                  taxclass_present =as.factor(taxclass_present),
                  b_class_present = as.factor(b_class_present),
                    b_class_group)])

dt_c[, saleprice_wo := tend_outliers_keep(saleprice, sigma = 3),.(borough)]
dt_c[, saleprice_wo_log := log(saleprice_wo)]

dt_c[, saleprice_log_wo := tend_outliers_keep(saleprice_log, sigma = 3),.(borough)]

price_summaries = dt_c[, as.list(summary(saleprice)), by = borough]
price_summaries
price_summaries = dt_c[, as.list(summary(saleprice_wo)), by = borough]
price_summaries

dt_molten = dt_c[,.(borough,saleprice,saleprice_log,saleprice_log_wo,saleprice_wo,saleprice_wo_log,saleprice_sqrt)] %>%
    melt.data.table(id.vars = c("borough"))
options(repr.plot.width = 10, repr.plot.height = 10, repr.plot.res = 200)
ggplot(data = dt_molten ,aes(x = value, fill = as.factor(borough)))+ 
  facet_wrap(variable ~ borough, scales ="free", ncol = 5) + 
  geom_density() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

id_cols = c("residential_group","commerical_group","totalunit_group","borough","taxclass_present","b_class_present","b_class_group","grosssquarefeet_group","grosssquarefeet_log_group","landsquarefeet_group","yearbuilt_group","address")
selected_cols = c('saleprice_log_wo')

options(repr.plot.width = 6, repr.plot.height = 3, repr.plot.res = 200)
for(i in id_cols){
    print(draw_boxplot(dt_c,id_col = i, selected_cols))
}

dt_c[,totalunits_group := ifelse(totalunits<4,totalunits,4)]
dt_c[,commercialunits_group := ifelse(commercialunits<2,commercialunits,2)]
dt_c[,yearbuilt_group := Hmisc::cut2(yearbuilt, g = 5)]
dt_c[,grosssquarefeet_log_group := Hmisc::cut2(grosssquarefeet_log, g = 5)]
dt_c[,saleprice_log_wo_group := Hmisc::cut2(saleprice_log_wo,g = 5),.(borough)]


options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(data = dt_c, aes(y = saleprice_log_wo, fill = borough)) + 
    geom_boxplot() +
    facet_grid(borough ~ totalunits_group,scales = "free")

options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(data = dt_c, aes(y = saleprice_log_wo, fill = borough)) + 
    geom_boxplot() +
    facet_grid(borough ~ commercialunits_group,scales = "free")

options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(data = dt_c, aes(y = saleprice_log_wo, fill = yearbuilt_group)) + 
    geom_boxplot() +
    facet_grid(borough ~ yearbuilt_group,scales = "free")

options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(dt_c, aes(x = yearbuilt, y = saleprice_log_wo, fill = as.factor(totalunits_group), color = as.factor(totalunits_group))) + geom_point() + facet_wrap(~borough) 

options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(dt_c, aes(x = yearbuilt, y = saleprice_log_wo, fill = as.factor(grosssquarefeet_log_group), color = as.factor(grosssquarefeet_log_group))) + geom_point() + facet_wrap(~borough) 

dt_c[, yearbuilt_group := ifelse(yearbuilt < 1900,1,ifelse(yearbuilt < 1950,2,3))]

options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(data = dt_c, aes(y = saleprice_log_wo, fill = borough)) + 
    geom_boxplot() +
    facet_grid(borough ~ yearbuilt_group,scales = "free")

ggplot(dt_c, aes(x = yearbuilt, y = totalunit_group, fill = as.factor(grosssquarefeet_log_group), color = as.factor(grosssquarefeet_log_group))) + geom_point() + facet_wrap(~borough) 

ggplot(data = dt_c ,aes(x = grosssquarefeet_log, fill = as.factor(borough)))+ 
  facet_wrap( ~ borough, scales ="free") + 
  geom_density() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

#tempData <- mice(dt_c[,.(borough,yearbuilt_group,address,grosssquarefeet,zipcode)] ,m=5,maxit=50,meth='pmm',seed=500)
#completedData <- complete(tempData,1)
dt_c[,grosssquarefeet_log_filled := grosssquarefeet_log]
dt_c[,grosssquarefeet_log_filled := fill_missing(grosssquarefeet_log_filled,method = "mean"),.(borough,totalunit_group)]

#dt_c[,grosssquarefeet_filled := completedData$grosssquarefeet]

dt_c[,grosssquarefeet_log_group := Hmisc::cut2(grosssquarefeet_log_filled, g = 5)]

table(dt_c$grosssquarefeet_log_group)

options(repr.plot.width = 12, repr.plot.height = 6, repr.plot.res = 200)
ggplot(dt_c, aes(x = yearbuilt, y = saleprice_log_wo, fill = as.factor(grosssquarefeet_log_group), color = as.factor(grosssquarefeet_log_group))) + geom_point() + facet_wrap(~borough) 

options(repr.plot.width = 7, repr.plot.height = 6, repr.plot.res = 200)
ggplot(data = dt_c, aes(y = saleprice_log_wo, fill = grosssquarefeet_log_group)) + 
    geom_boxplot() +
    facet_grid(borough ~ grosssquarefeet_log_group,scales = "free")

dt[, saleprice_log := log(saleprice)]
dt[, saleprice_wo := tend_outliers_keep(saleprice, sigma = 3),.(borough)]
dt[, saleprice_wo_log := log(saleprice_wo)]
dt[, saleprice_log_wo := tend_outliers_keep(saleprice_log, sigma = 3),.(borough)]

dt[, yearbuilt_group := ifelse(yearbuilt < 1900,1,ifelse(yearbuilt < 1950,2,3))]
dt[, totalunits_group := ifelse(totalunits<4,totalunits,4)]
dt[, commercialunits_group := ifelse(commercialunits<2,commercialunits,2)]


dt[,grosssquarefeet_log_filled := log(grosssquarefeet)]
dt[,grosssquarefeet_log_filled := fill_missing(grosssquarefeet_log_filled,method = "mean"),.(borough,totalunits_group)]
dt[,grosssquarefeet_log_group := Hmisc::cut2(grosssquarefeet_log_filled, g = 5)]

dt[, commercialunits_sqrt := sqrt(commercialunits)]
dt[, residentialunits_sqrt := sqrt(residentialunits)]

dt[,residentialunits_group := Hmisc::cut2(residentialunits_sqrt, g = 5)]
dt[,residentialunits_group := encode_numeric(residentialunits_group)]

options(repr.plot.width = 10, repr.plot.height = 2, repr.plot.res = 200)
ggplot(data = dt ,aes(x = residentialunits_sqrt, fill = as.factor(borough)))+ 
  facet_wrap( ~ borough, scales ="free", ncol = 5 ) + 
  geom_density() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

building_cols = c("residentialunits_group","commercialunits_group","grosssquarefeet_log_filled")
dt_cluster =  copy(scale(dt[,.SD,.SDcols = building_cols ]))

set.seed(0)
building_clusters <- kmeans(dt_cluster, centers = 5, nstart = 25)
table(building_clusters$cluster)
building_clusters

dt$building_clusters = building_clusters$cluster

dt_c = copy(dt)
dt_c$borough = as.factor(dt_c$borough)


options(repr.plot.width = 10, repr.plot.height = 10, repr.plot.res = 200) # for graph sizes
ggplot(data = dt_c[,.(saleprice = mean(saleprice_wo, na.rm = TRUE)),.(saledate,borough)]
       , aes(x = saledate, y = saleprice, group = borough, color = borough)) +
    geom_line() +
    facet_wrap(~borough, ncol = 1,scales = "free")

## without outliers
options(repr.plot.width = 10, repr.plot.height = 15, repr.plot.res = 200) # for graph sizes
ggplot(data = dt_c[,.(saleprice = mean(saleprice_wo, na.rm = TRUE)),.(saledate,b_class_group)]
       , aes(x = saledate, y = saleprice, group = b_class_group, color = b_class_group)) +
    geom_line() +
    facet_wrap(~b_class_group, ncol = 1,scales = "free")

dt[, saleprice_wo := tend_outliers_keep(saleprice, sigma = 3),.(borough)]
dt[, saleprice_wo_3s := tend_outliers_keep(saleprice, sigma = 3),.(borough,b_class_group)]
dt[, saleprice_wo_IQR := tend_outliers_keep_IQR(saleprice, IQR = 1.5),.(borough,b_class_group)]

dt[, saleprice_log_wo_IQR := tend_outliers_keep_IQR(saleprice_log,  IQR = 1.5),.(borough,b_class_group)]
dt[, saleprice_log_wo_3s := tend_outliers_keep(saleprice_log, sigma = 3),.(borough,b_class_group)]

summary( dt[,.(saleprice,saleprice_wo,saleprice_wo_3s,saleprice_wo_IQR
               ,saleprice_log_wo= exp(saleprice_log_wo)
               ,saleprice_log_wo_IQR = exp(saleprice_log_wo_IQR)
               ,saleprice_log_wo_3s = exp(saleprice_log_wo_3s))])

dt_molten = dt[,.(borough,saleprice,saleprice_wo,saleprice_wo_3s,saleprice_wo_IQR
               ,saleprice_log_wo
               ,saleprice_log_wo_IQR 
               ,saleprice_log_wo_3s)] %>%
    melt.data.table(id.vars = c("borough"))
options(repr.plot.width = 10, repr.plot.height = 15, repr.plot.res = 200)
ggplot(data = dt_molten ,aes(x = value, fill = as.factor(borough)))+ 
  facet_wrap(variable ~ borough, scales ="free", ncol = 5) + 
  geom_density() + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

dt_outlier = dt[,.SD,.SDcols = c("saledate","b_class_group","saleprice_wo","saleprice_wo_3s","saleprice_wo_IQR")]
dt_outlier[, yearmonth := zoo::as.yearmon(saledate, "%Y%m")] 
dt_outlier = dt_outlier[,.(saleprice_wo = mean(saleprice_wo),
             saleprice_wo_3s = mean(saleprice_wo_3s),
             saleprice_wo_IQR = mean(saleprice_wo_IQR)),
          .(yearmonth,b_class_group)]
dt_molten = dt_outlier %>%
    melt.data.table(id.vars = c("yearmonth","b_class_group"))

options(repr.plot.width = 10, repr.plot.height = 5, repr.plot.res = 200) # for graph sizes
ggplot(data = dt_molten
       , aes(x = yearmonth, y = value, group = b_class_group, color = b_class_group)) +
    geom_line() + facet_wrap(~variable,scales = "free", ncol = 1)

#dt[, wday := wday(saledate, label=TRUE)]
dt_outlier = dt[,.SD,.SDcols = c("saledate","b_class_group","saleprice_wo","saleprice_wo_3s","saleprice_wo_IQR")]
dt_outlier[, wday := wday(saledate, label=TRUE)] 
dt_outlier = dt_outlier[,.(saleprice_wo = mean(saleprice_wo),
             saleprice_wo_3s = mean(saleprice_wo_3s),
             saleprice_wo_IQR = mean(saleprice_wo_IQR)),
          .(wday,b_class_group)]
dt_molten = dt_outlier %>%
    melt.data.table(id.vars = c("wday","b_class_group"))

options(repr.plot.width = 10, repr.plot.height = 5, repr.plot.res = 200) # for graph sizes
ggplot(data = dt_molten
       , aes(x = wday, y = value, group = b_class_group, color = b_class_group)) +
    geom_line() + facet_wrap(~variable,scales = "free", ncol = 1)

table(dt$totalunits)
dt[,iszero := ifelse(totalunits == 0,"1","0")]

options(repr.plot.width = 5, repr.plot.height = 3, repr.plot.res = 200) # for graph sizes
ggplot(data = dt, aes(x = b_class_group, fill = as.factor(iszero), group = as.factor(iszero))) + geom_bar() 

options(repr.plot.width = 5, repr.plot.height = 3, repr.plot.res = 200) # for graph sizes
ggplot(data = dt[b_class_group == "other"], aes(x = taxclassatpresent, fill = as.factor(iszero), group = as.factor(iszero))) + geom_bar() 

#dt[residentialunits + commercialunits != totalunits,.N,.(bor)]
#t(dt[idx == 200])

dt[(residentialunits + commercialunits != totalunits),.N,.(taxclass_present)]
dt[(residentialunits + commercialunits != totalunits),.N,.(buildingclassatpresent)][order(-N)] %>% head()
dt[(residentialunits + commercialunits != totalunits),.N,.(buildingclassatpresent)][order(-N)] %>% head() %>% select(N) %>% sum()

skim(dt[zipcode == 0]) #308 records

## deletion
dt = dt[zipcode != 0] # 308 rows

dt[,iszero := ifelse(is.na(grosssquarefeet),"1","0")]

ggplot(data = dt[totalunits < 10], aes(x = as.factor(totalunits), fill = as.factor(iszero), group = as.factor(iszero))) + geom_bar() + facet_wrap(~b_class_group)

dt[, saleprice_log := log(saleprice)]

draw_boxplot(dt,id_col = "taxclassatpresent", "saleprice_log")

# by using the info on https://www1.nyc.gov/site/finance/taxes/property-determining-your-assessed-value.page
dt[, assessment_ratio_present := ifelse(taxclass_present == 1,0.06,0.45)]
dt[,onlycommercial := ifelse(totalunits == commercialunits,1,0)]

# maybe new feature?
a = dt[,.N,.(onlycommercial,neighborhood)]
onlycommercial_neighborhoods = a[,.N,.(neighborhood)][N == 1]$neighborhood

nrow(dt[neighborhood %in% onlycommercial_neighborhoods])
#nah, nothing important

#maybe degree of commercial?
a[,sum_N := sum(N),.(neighborhood)]
a=a[onlycommercial == 1, .(ratio = N / sum_N,neighborhood)]
options(repr.plot.width =3, repr.plot.height = 3, repr.plot.res = 200) # for graph sizes
hist(a$ratio)
highlycommercial_neighborhoods = a[ratio > 0.4]$neighborhood

nrow(dt[neighborhood %in% highlycommercial_neighborhoods])
#cool

dt[,highly_commercial := ifelse(neighborhood %in% highlycommercial_neighborhoods,1,0)]

encode_cols = c("b_class_present","b_class_group","address","taxclassatpresent")
dt[,paste0((encode_cols),"_encoded"):= lapply(.SD, encode_numeric), .SDcols = encode_cols]

dt[,address_encoded := encode_numeric(address)]
dt[,b_class_group_encoded := encode_numeric(b_class_group)]
dt[,taxclassatpresent_encoded := encode_numeric(taxclassatpresent)]
dt[,b_class_present_encoded := encode_numeric(b_class_present)]

dt[,grosssquarefeet_log_group_encoded := encode_numeric(grosssquarefeet_log_group)]

dt[, commercialunits_log := log(commercialunits+0.01)]
dt[, residentialunits_log := log(residentialunits+0.01)]

dt[, commercialunits_wo := tend_outliers_keep_IQR(commercialunits, IQR = 1.5)]
dt[, commercialunits_log := log(commercialunits_wo+0.01)]

dt_molten = dt %>% purrr::keep(is.numeric) %>% 
  tidyr::gather()

options(repr.plot.width=12, repr.plot.height=15) # for graph sizes
ggplot(data = dt_molten,aes(x = value, fill = key))+ 
  facet_wrap(~ key, scales = "free", ncol = 4) + 
  geom_density(fill = "green") + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

#feature_list = c("borough","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")
feature_list = c("borough","residentialunits_group","commercialunits_group","address_encoded","b_class_present_encoded","taxclassatpresent_encoded","highly_commercial","building_clusters")

target = c("saleprice_log_wo","saleprice_log")

dt_model = copy(dt[,.SD,.SDcols = c("idx",target,feature_list)])

chunk_no = 10
set.seed(0)
folds <- cut(seq(1,nrow(dt_model)),breaks=chunk_no,labels=FALSE)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

for(i in 1:chunk_no){
  #Segment your data by fold using the which() function 

  testIndexes <- which(folds==i,arr.ind=TRUE)
  testData    <- dt_model[testIndexes, ]
  trainData   <- dt_model[-testIndexes, ]
    
    target = "saleprice_log_wo" 
   y_train        = trainData[[target]]
    target = "saleprice_log"
   y_test         = testData[[target]]
    
    Scale_Parameters = get_scale_params(trainData, feature_list)
    x_train = scale(trainData[,.SD,.SDcols = feature_list])
    
    x_test = testData[,.SD,.SDcols = feature_list]
    scale_external(x_test,Scale_Parameters)
    
    ls.model <- cv.glmnet(  x_train , y_train , type.measure="mse", alpha=1, family="gaussian", nfolds = 5)
    lasso_imp = coef(ls.model)
    lasso_imp = t(t(lasso_imp[order(lasso_imp),]))
    lasso_imp = data.table("names" = names(lasso_imp[,1]), "coeff" = lasso_imp[,1])
    
     if(str_detect(target,"log") == TRUE){
      pred  = exp(predict(ls.model, as.matrix(x_test), s = "lambda.min"))
      actual = exp(y_test)
      
      fitted = exp(predict(ls.model, as.matrix(x_train), s = "lambda.min"))
  }else{
      pred  = predict(ls.model, as.matrix(x_test), s = "lambda.min")
      actual = y_test
      
      fitted = exp(predict(ls.model, as.matrix(x_train)))
  }

  #Check performance
  sub_pred_table = testData[,.(idx, actual = actual, pred = pred, chunk = i)]
  sub_fitted_table = trainData[,.(idx, fitted = fitted, chunk = i )]
  
  pred_table = rbind(pred_table,sub_pred_table )
  fitted_table = rbind(fitted_table,sub_fitted_table )
 
}   


#feature_list = c("borough","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")
feature_list = c("borough","residentialunits_group","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")

target = "saleprice_log"

dt_model = copy(dt[,.SD,.SDcols = c("idx",target,feature_list)])

chunk_no = 10
set.seed(0)
folds <- cut(seq(1,nrow(dt_model)),breaks=chunk_no,labels=FALSE)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

#for(i in 1:chunk_no){
#  #Segment your data by fold using the which() function 
#
#  testIndexes <- which(folds==i,arr.ind=TRUE)
#  testData    <- dt_model[testIndexes, ]
#  trainData   <- dt_model[-testIndexes, ]
#  
#   y_train        = trainData[[target]]
#   y_test         = testData[[target]]
#    
#    Scale_Parameters = get_scale_params(trainData, feature_list)
#    x_train = scale(trainData[,.SD,.SDcols = feature_list])
#    
#    x_test = testData[,.SD,.SDcols = feature_list]
#    scale_external(x_test,Scale_Parameters)
#    
#    for (k in c(5)){ #3,5,10,15 
#    knn = caret::knnregTrain(train = x_train, test = x_test, y = y_train, k = k)
#    print(paste0("knn k= ",k,"  rmse: ",calc_rmse(y_test, knn)))
#    }
#      
#     if(str_detect(target,"log") == TRUE){
#      pred  = exp(knn)
#      actual = exp(y_test)
#  }else{
#      pred  = knn
#      actual = y_test
#  }
#
#  #Check performance
#  sub_pred_table = testData[,.(idx, actual = actual, pred = pred, chunk = i)]
#  sub_fitted_table = trainData[,.(idx, fitted = fitted, chunk = i )]
#  
#  pred_table = rbind(pred_table,sub_pred_table )
#  fitted_table = rbind(fitted_table,sub_fitted_table )
# 
#}   
#

#feature_list = c("borough","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")
feature_list = c("borough","residentialunits_group","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")

target = "saleprice_log"

dt_model = copy(dt[,.SD,.SDcols = c("idx",target,feature_list)])

chunk_no = 10
set.seed(0)
folds <- cut(seq(1,nrow(dt_model)),breaks=chunk_no,labels=FALSE)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

for(i in 1:1){
  #Segment your data by fold using the which() function 

  testIndexes <- which(folds==i,arr.ind=TRUE)
  testData    <- dt_model[testIndexes, ]
  trainData   <- dt_model[-testIndexes, ]
  
   y_train        = trainData[[target]]
   y_test         = testData[[target]]
    
    Scale_Parameters = get_scale_params(trainData, feature_list)
    x_train = scale(trainData[,.SD,.SDcols = feature_list])
    
    x_test = testData[,.SD,.SDcols = feature_list]
    scale_external(x_test,Scale_Parameters)
    
    svm.model <- svm(  x_train , y_train)
      
     if(str_detect(target,"log") == TRUE){
      pred  = exp(predict(svm.model, as.matrix(x_test)))
      actual = exp(y_test)
  }else{
      pred  = predict(svm.model, as.matrix(x_test))
      actual = y_test
      
      fitted = exp(predict(svm.model, as.matrix(x_train)))
  }

  #Check performance
  sub_pred_table = testData[,.(idx, actual = actual, pred = pred, chunk = i)]
  sub_fitted_table = trainData[,.(idx, fitted = fitted, chunk = i )]
  
  pred_table = rbind(pred_table,sub_pred_table )
  fitted_table = rbind(fitted_table,sub_fitted_table )
 
}   


## Results for only 1 chunk
print("overall test rmse:")
calc_rmse(pred_table$pred,pred_table$actual)
calc_rmse(pred_table[actual < 20000000]$pred,pred_table[actual < 20000000]$actual)


params = list(   booster = "gbtree"
                 #  , eta = best_params$eta #learning rate
                 #  , gamma = best_params$gamma # min loss reduction
                 #   , max_depth = best_params$depth
                 , min_child_weight = 1, subsample = 1, colsample_bytree= 1
                 , objective = "reg:squarederror"
                 , eval_metric = "rmse")

#feature_list = c("borough","zipcode","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")
feature_list = c("borough","b_class_group_encoded"
                 ,"zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                )
target = "saleprice"

fit = model_xgboost(feature_list,target,chunk_no = 10)
pred_table = fit[[1]]

imp_table = fit[[2]]
imp_table

print("overall test rmse:")
calc_rmse(pred_table$pred,pred_table$actual)
calc_rmse(pred_table[actual < 20000000]$pred,pred_table[actual < 20000000]$actual)


print("please compare with knn:")
calc_rmse(pred_table[chunk ==1]$pred,pred_table[chunk ==1]$actual)

#feature_list = c("borough","zipcode","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")
feature_list = c("borough","b_class_group_encoded"
                 ,"zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                )
target = "saleprice_log"


fit = model_xgboost(feature_list,target,chunk_no = 10)
pred_table = fit[[1]]

imp_table = fit[[2]]
imp_table

print("overall test rmse:")
calc_rmse(pred_table$pred,pred_table$actual)
calc_rmse(pred_table[actual < 20000000]$pred,pred_table[actual < 20000000]$actual)


## units groups vs log versions

feature_list = c("borough","b_class_group_encoded"
                 ,"zipcode","commercialunits_log","residentialunits_log","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                 )
target = "saleprice_log"


fit = model_xgboost(feature_list,target,chunk_no = 10)
pred_table = fit[[1]]

imp_table = fit[[2]]
imp_table
## target = saleprice
print("overall test rmse:")
calc_rmse(pred_table$pred,pred_table$actual)
calc_rmse(pred_table[actual < 20000000]$pred,pred_table[actual < 20000000]$actual)


#feature_list = c("borough","zipcode","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded")
feature_list = c("borough","b_class_group_encoded"
                 ,"commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                 ,"grosssquarefeet_log_group_encoded" ## replacable with zipcode
                )
target = "saleprice_log"


fit = model_xgboost(feature_list,target,chunk_no = 10)
pred_table = fit[[1]]

imp_table = fit[[2]]
imp_table
## target = saleprice
print("overall test rmse:")
calc_rmse(pred_table$pred,pred_table$actual)
calc_rmse(pred_table[actual < 20000000]$pred,pred_table[actual < 20000000]$actual)


options(repr.plot.width = 10, repr.plot.height = 5, repr.plot.res = 200) # for graph sizes
p1 = ggplot(data = pred_table, aes(x = actual, y = pred, color = as.factor(chunk))) + geom_point() + geom_abline(intercept = 0, slope = 1)+ theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))
p2 = ggplot(data = pred_table[actual < 20000000], aes(x = actual, y = pred, color = as.factor(chunk))) + geom_point() + geom_abline(intercept = 0, slope = 1) + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

grid.arrange(p1,p2, ncol = 2)

options(repr.plot.width = 10, repr.plot.height = 5, repr.plot.res = 200) # for graph sizes
ggplot(data = pred_table[actual < 20000000,.(actual, pred, borough = dt[saleprice < 20000000]$borough)]
       , aes(x = actual, y = pred, color = as.factor(borough))) + geom_point() + geom_abline(intercept = 0, slope = 1) + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))


feature_list = c( "zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                )
target = "saleprice"

fit_bb = model_xgboost_partial(feature_list,target,chunk_no = 5)

pred_table_bb = fit_bb[[1]]

imp_table_bb = fit_bb[[2]]
imp_table_bb
## target = saleprice
print("overall test rmse:")
calc_rmse(pred_table_bb$pred,pred_table_bb$actual)
calc_rmse(pred_table_bb[actual < 20000000]$pred,pred_table_bb[actual < 20000000]$actual)


feature_list = c( "zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                )
target = "saleprice_log"

fit_bb = model_xgboost_partial(feature_list,target,chunk_no = 5)

pred_table_bb = fit_bb[[1]]

imp_table_bb = fit_bb[[2]]
imp_table_bb
## target = saleprice
print("overall test rmse:")
calc_rmse(pred_table_bb$pred,pred_table_bb$actual)
calc_rmse(pred_table_bb[actual < 20000000]$pred,pred_table_bb[actual < 20000000]$actual)


options(repr.plot.width = 10, repr.plot.height = 5, repr.plot.res = 200) # for graph sizes
p1 = ggplot(data = pred_table_bb, aes(x = actual, y = pred, color = as.factor(chunk))) + geom_point() + geom_abline(intercept = 0, slope = 1)+ theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))
p2 = ggplot(data = pred_table_bb[actual < 20000000], aes(x = actual, y = pred, color = as.factor(chunk))) + geom_point() + geom_abline(intercept = 0, slope = 1) + theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

grid.arrange(p1,p2, ncol = 2)

#imp_table_bb = imp_table_bb[order(-avg_gain)]
#imp_table_bb[, .SD[1], .(borough,b_class_group)][order(-avg_gain)]

dt_tree = imp_table_bb[,.(M = mean(avg_gain, na.rm = TRUE), N = .N) ,.(b_class_group,Feature)]

options(repr.plot.width = 8, repr.plot.height = 5, repr.plot.res = 200)
ggplot(dt_tree
       , aes(area = M, fill = N, label = Feature,subgroup = b_class_group)) +
  geom_treemap() +
 geom_treemap_subgroup_border() +
  geom_treemap_subgroup_text(place = "centre", grow = T, alpha = 0.5, colour =
                             "black", fontface = "italic", min.size = 0) +
  geom_treemap_text(colour = "white", place = "topleft", reflow = T)

ggplot(data = pred_table_bb[actual < 20000000, .(actual,pred,chunk,borough = dt[saleprice <20000000]$borough, b_class_group = dt[saleprice <20000000]$b_class_group)],
       aes(x = actual, y=pred, group = as.factor(chunk), color = as.factor(chunk))) + 
    geom_point() +
    facet_grid(borough~b_class_group) + 
    geom_abline(intercept = 0, slope = 1) + 
    theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5))

options(repr.plot.width = 5, repr.plot.height = 3, repr.plot.res = 200) # for graph sizes
ggplot(data =  pred_table_bb[, .(rmse= calc_rmse(pred,actual)),.(borough, b_class_group)],
      aes(x = as.factor(borough), y = rmse, group = as.factor(b_class_group), color = as.factor(b_class_group))) + geom_point() 

## Both feature lists work nice
#feature_list = c("zipcode","residentialunits_log","commercialunits_log","address_encoded","taxclassatpresent_encoded","grosssquarefeet")
feature_list = c( "zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                )

train_target = "saleprice_wo"
test_target = "saleprice"

fit_bb_wo = model_xgboost_partial_wo(feature_list,train_target,test_target,chunk_no = 5)

pred_table_bb_wo = fit_bb_wo[[1]]

imp_table_bb_wo = fit_bb_wo[[2]]
imp_table_bb_wo

print("overall test rmse:")
calc_rmse(pred_table_bb_wo$pred,pred_table_bb_wo$actual)
calc_rmse(pred_table_bb_wo[actual < 20000000]$pred,pred_table_bb_wo[actual < 20000000]$actual)


colnames(dt)

feature_list = c( "zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                ,"grosssquarefeet_log_filled")

train_target = "saleprice_log_wo"
test_target = "saleprice_log"

fit_bb_wo = model_xgboost_partial_wo(feature_list,train_target,test_target,chunk_no = 5)

pred_table_bb_wo = fit_bb_wo[[1]]

imp_table_bb_wo = fit_bb_wo[[2]]

print("overall test rmse:")
calc_rmse(pred_table_bb_wo$pred,pred_table_bb_wo$actual)
calc_rmse(pred_table_bb_wo[actual < 20000000]$pred,pred_table_bb_wo[actual < 20000000]$actual)

#imp_table_bb = imp_table_bb[order(-avg_gain)]
#imp_table_bb[, .SD[1], .(borough,b_class_group)][order(-avg_gain)]
dt_tree = imp_table_bb_wo[,.(M = mean(avg_gain, na.rm = TRUE), N = .N) ,.(b_class_group,Feature)]

options(repr.plot.width = 8, repr.plot.height = 5, repr.plot.res = 200)
ggplot(dt_tree
       , aes(area = M, fill = N, label = Feature,subgroup = b_class_group)) +
  geom_treemap() +
 geom_treemap_subgroup_border() +
  geom_treemap_subgroup_text(place = "centre", grow = T, alpha = 0.5, colour =
                             "black", fontface = "italic", min.size = 0) +
  geom_treemap_text(colour = "white", place = "topleft", reflow = T)

feature_list = c( "commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                ,"grosssquarefeet_log_filled")

train_target = "saleprice_log_wo"
test_target = "saleprice_log"

fit_bb_wo = model_xgboost_partial_wo(feature_list,train_target,test_target,chunk_no = 5)

pred_table_bb_wo = fit_bb_wo[[1]]

imp_table_bb_wo = fit_bb_wo[[2]]

print("overall test rmse:")
calc_rmse(pred_table_bb_wo$pred,pred_table_bb_wo$actual)
calc_rmse(pred_table_bb_wo[actual < 20000000]$pred,pred_table_bb_wo[actual < 20000000]$actual)


#imp_table_bb = imp_table_bb[order(-avg_gain)]
#imp_table_bb[, .SD[1], .(borough,b_class_group)][order(-avg_gain)]
dt_tree = imp_table_bb_wo[,.(M = mean(avg_gain, na.rm = TRUE), N = .N) ,.(b_class_group,Feature)]

options(repr.plot.width = 8, repr.plot.height = 5, repr.plot.res = 200)
ggplot(dt_tree
       , aes(area = M, fill = N, label = Feature,subgroup = b_class_group)) +
  geom_treemap() +
 geom_treemap_subgroup_border() +
  geom_treemap_subgroup_text(place = "centre", grow = T, alpha = 0.5, colour =
                             "black", fontface = "italic", min.size = 0) +
  geom_treemap_text(colour = "white", place = "topleft", reflow = T)

feature_list = c( "zipcode","commercialunits_group","residentialunits_group","highly_commercial","onlycommercial"
                 ,"address_encoded","taxclass_present","building_clusters","assessment_ratio_present"
                ,"grosssquarefeet_log_filled")

target = "saleprice_log"

dt_model = copy(dt[b_class_group =="other",.SD,.SDcols = c("idx","b_class_group",target,feature_list)])

chunk_no = 10
set.seed(0)
folds <- cut(seq(1,nrow(dt_model)),breaks=chunk_no,labels=FALSE)

pred_table = data.table()
imp_table = data.table()
fitted_table = data.table()

for(i in 1:chunk_no){
  #Segment your data by fold using the which() function 

  testIndexes <- which(folds==i,arr.ind=TRUE)
  testData    <- dt_model[testIndexes, ]
  trainData   <- dt_model[-testIndexes, ]
  
   y_train        = trainData[[target]]
   y_test         = testData[[target]]
    
    Scale_Parameters = get_scale_params(trainData, feature_list)
    x_train = scale(trainData[,.SD,.SDcols = feature_list])
    
    x_test = testData[,.SD,.SDcols = feature_list]
    scale_external(x_test,Scale_Parameters)
    
  d_train= xgb.DMatrix(data = as.matrix(x_train), label = y_train)
  d_test = xgb.DMatrix(data = as.matrix(x_test), label = y_test)
  
  set.seed(i)
  xg.model = xgb.train( data = d_train, 
                        nrounds = 20,
                        early_stopping_rounds = 3,
                        params = params, 
                        watchlist = list(train = d_train, test = d_test))
  
  if(str_detect(target,"log") == TRUE){
      xg.pred  = exp(predict(xg.model, d_test))
      actual = exp(y_test)
      
      xg.fitted = exp(predict(xg.model, d_train))
  }else{
      xg.pred  = predict(xg.model, d_test)
      actual = y_test
      
      xg.fitted = exp(predict(xg.model, d_train))
  }
    
   imp = data.table(xgb.importance( feature_names = colnames(x_train), model = xg.model))
   imp_table = rbind(imp_table,data.table(chunk = i, imp))  
    
    
  #Check performance
  sub_pred_table = testData[,.(idx, actual = actual, pred = xg.pred, chunk = i)]
  sub_fitted_table = trainData[,.(idx, fitted = xg.fitted, chunk = i )]
  
  pred_table = rbind(pred_table,sub_pred_table )
  fitted_table = rbind(fitted_table,sub_fitted_table )
 
}   


pred_table = merge(pred_table, dt[,.(idx,b_class_present, taxclass_present)], by = "idx", all.x = TRUE )

options(repr.plot.width = 10, repr.plot.height = 10, repr.plot.res = 200) # for graph sizes

ggplot(data = pred_table[actual < 1000000 & pred < 750000], aes(x = actual, y = pred, color = as.factor(taxclass_present))) + geom_point() + 
geom_abline(intercept = 0, slope = 1) + 
theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust = 0.5)) +
facet_wrap(~b_class_present)


dt_ts = copy(dt)
dt_ts[, year := year(saledate)]
dt_ts[, wday := wday(saledate)]
dt_ts[, month := month(saledate)]
dt_ts[, week := week(saledate)]

month_dt= dt_ts[,.(month_avg_saleprice = mean(saleprice),
                   month_num_saleprice = .N),
                .(month,borough,b_class_group)]

month_dt = month_dt[order(month)]
month_dt[,`:=` (month_avg_saleprice  = shift(month_avg_saleprice,1,type = "lag"),
                month_num_saleprice  = shift(month_num_saleprice,1,type = "lag")),
         .(borough,b_class_group)]

week_dt= dt_ts[,.(week_avg_saleprice = mean(saleprice),
                  week_num_saleprice = .N),
               .(week,borough,b_class_group)]

week_dt = week_dt[order(week)]
week_dt[,`:=` ( week_avg_saleprice  = shift(week_avg_saleprice,1,type = "lag"),
                week_num_saleprice  = shift(week_num_saleprice,1,type = "lag")),
         .(borough,b_class_group)]

dt_ts = merge(dt_ts,month_dt, by = c("borough","b_class_group","month") )
dt_ts = merge(dt_ts,week_dt, by = c("borough","b_class_group","week") )

dt_ts = dt_ts[order(saledate)]

params = list(   booster = "gbtree"
                 #  , eta = best_params$eta #learning rate
                 #  , gamma = best_params$gamma # min loss reduction
                 #   , max_depth = best_params$depth
                 , min_child_weight = 1, subsample = 1, colsample_bytree= 1
                 , objective = "reg:squarederror"
                 , eval_metric = "rmse")

feature_list = c("borough","zipcode","residentialunits","commercialunits","address_encoded","b_class_present_encoded","taxclassatpresent_encoded","week_avg_saleprice","week_num_saleprice","month_avg_saleprice","month_num_saleprice")
target = "saleprice"

dt_ts_model = copy(dt_ts[,.SD,.SDcols = c("idx","month","year",target,feature_list)])

imp_table = data.table()
xg_preds = c()
for(i in c(1:7)){
  
    x_train_sub = dt_ts_model[(month <= i & year == 2017)| year == 2016,.SD,.SDcols = feature_list]
    Scale_Parameters = get_scale_params(x_train_sub)
    x_train_sub = scale(x_train_sub, center = TRUE, scale = TRUE)
  
    
    x_test_sub  = dt_ts_model[((month == i+1) & year == 2017) ,.SD,.SDcols = feature_list]
    scale_external(x_test_sub,Scale_Parameters)
    
    y_train_sub = dt_ts_model[(month <= i & year == 2017)| year == 2016][[target]]
    y_test_sub  = dt_ts_model[(month == 1+i) & year == 2017][[target]]
    
    d_train_sub= xgb.DMatrix(data = as.matrix(x_train_sub), label = y_train_sub)
    d_test_sub = xgb.DMatrix(data = as.matrix(x_test_sub), label = y_test_sub)
    
    set.seed(0)
    xg.model_sub = xgb.train( data = d_train_sub, 
                              nrounds = 30,
                              early_stopping_rounds = 3,
                              params = params, 
                              watchlist = list(train = d_train_sub, test = d_test_sub))
    
    imp = data.table(xgb.importance( feature_names = colnames(x_train_sub), model = xg.model_sub))
    imp_table = rbind(imp_table,data.table(month = i, imp))
    
    xg.pred_sub  = predict(xg.model_sub, d_test_sub)
    pred = xg.pred_sub
    xg_preds = c(xg_preds,pred)  
  
}

imp_table_2= dcast(imp_table, Feature ~ month, value.var = "Gain")
imp_table_2[order(-`5`)]


print("overall test rmse:")
calc_rmse(pred_table$pred,pred_table$actual)
calc_rmse(pred_table[actual < 20000000]$pred,pred_table[actual < 20000000]$actual)

pred_table_bb_wo[, error := actual - pred]

pred_table_bb_wo[order(-abs(error))] %>% head(10)

selected_data = pred_table_bb_wo[abs(error)> (mean(error)*1.6)]
selected_data = dt[idx %in% selected_data$idx]
nrow(selected_data)

selected_list = c("saleprice_log","borough","block","lot","zipcode","residentialunits","commercialunits","yearbuilt","assessment_ratio_present","address_encoded","b_class_group_encoded","taxclassatpresent_encoded")
selected_data = selected_data[,.SD,.SDcols = selected_list]

Scale_Parameters = get_scale_params(dt, selected_list)
scale_external(selected_data,Scale_Parameters)

set.seed(200)
clusters <- kmeans(selected_data, centers = 3, nstart= 15)

clusters

table(clusters$cluster)

unique(dt[,.(address, address_encoded)])

table(dt$taxclassatpresent)

#       with nys as (
#       select nyx.* 
#        ,case when SALE_PRICE = '-' or SALE PRICE IS NULL then 0 else SALE_PRICE end as SALE_PRICE_cor
#        ,COALESCE(grosssquarefeet,0) as grosssquarefeet_cor
#       from nyx_rolling_sales nyx
#       ),
#       stats as (
#       select nys.*    
#           ,avg(SALE_PRICE_cor) over() as mean
#           ,stddev(SALE_PRICE_cor) over () as sd 
#           ,avg(SALE_PRICE_cor) over(partition by NEIGHBORHOOD,BUILDING_CLASS) as mean_nb
#           ,stddev(SALE_PRICE_cor) over (partition by NEIGHBORHOOD,BUILDING_CLASS) as sd_nb
#       from nys 
#       )
#       select s.*
#           , COALESCE(TRY((s.SALE_PRICE_cor - s.mean) / s.sd),0) as sale_price_zscore -- a
#           , COALESCE(TRY((s.SALE_PRICE_cor - s.mean_nb) / s.sd_nb),0) as sale_price_zscore_neighborhood --b
#           , COALESCE(TRY(grosssquarefeet_cor/totalunits),0) as square_ft_per_unit --c
#           , COALESCE(TRY(s.SALE_PRICE_cor/totalunits),0) as price_per_unit --c
#       from stats s
#       
