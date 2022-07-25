#!/usr/bin/env python2
# -*- coding: utf-8 -*-
"""
Created on Tue May  4 12:44:49 2022

@author: carlos
"""


import networkx as nx

import matplotlib.pyplot as plt

from networkx.algorithms import community
import time
import itertools
import random
import copy
import numpy
import json
import sys
import os
import pulp
import math
import pickle
import operator


import domainConfiguration
#ILP_METHOD = True
ILP_METHOD = False
verbose_log = True
#numNodes = 10
populationSize=100 
mutationProb=0.3
#crossoverProb=0.8
crossoverProb=0.95

numberGenerations = 100 
loglevel = 0
repeatedSolutions = False

ACTUAL_GENERATION = None

SECONDS2MS = 1000
SECONDS2MCRS = 1000000
MS2SECONDS = float(1/1000)

scaleOptimizationTime = SECONDS2MS
scaleResponseTime = MS2SECONDS


randomSeeds=2022

random.seed(randomSeeds)
numpy.random.seed(randomSeeds)
random_state = numpy.random.RandomState(randomSeeds)



appNumberRange = range(20,61,20)


nodeNumberRange = range(100,301,100)


experiments2execute = list()

for appNumber in appNumberRange:
    for nodeNumber in nodeNumberRange:
        oneExperiment = (appNumber,nodeNumber)
        experiments2execute.append(oneExperiment)


PRINTS_X = False






def print_x(msg):
    if PRINTS_X:
        print(msg)
        

def printlog(text,level):
    if loglevel >= level:
        print(text)


# NOTE: X, ??
def checkConstraints(chrCol,chrSer):
    return True





#******************************************************************************************
#   Control cases (cloud, centralities)
#******************************************************************************************


def getOnlyOneColony():
    
    oneColonySolution = [0 for element in range(len(GAstructure4partition))]
    oneColonySolution[0]=1
    
    solServ,solCloud,solTimes,solFreeResources = allocateServicesInColonies(oneColonySolution)
    
    oneColonyFitness=calculateFitnessObjectives(oneColonySolution,solServ, solCloud, solTimes, solFreeResources)
    
    oneColonyOptimizationTime = oneColonyFitness['max_allocation_time']
    oneColonyResponseTime = oneColonyFitness['estimated_latency']
    
    return oneColonyOptimizationTime,oneColonyResponseTime




def getCentralityAwareColony(size):




    CentralityAwareSolution = [0 for element in range(len(GAstructure4partition))]
    for i in range(len(GAstructure4partition)):
        if len(GAstructure4partition[i]['Cxi'])>=(size-1) and len(GAstructure4partition[i]['Cxi'])<=(size+1):
            #print(GAstructure4partition[i]['Cxi'])
            CentralityAwareSolution[i]=1

    repairSolution2MoreColonies(CentralityAwareSolution,GAstructure4partition) #si hay colonies que se solapan, pues las arreglo dividiendo las colonies
    repairAllInColoniesLess(CentralityAwareSolution,GAstructure4partition)  #incluyo los nodos que no estan en ninguna colony en el menor numero de colonies posible

    
    solServ,solCloud,solTimes,solFreeResources = allocateServicesInColonies(CentralityAwareSolution)
    
    centralityAwareFitness=calculateFitnessObjectives(CentralityAwareSolution,solServ, solCloud, solTimes, solFreeResources)
    
    print(size)
    print(centralityAwareFitness)
    
    centralityAwareOptimizationTime = centralityAwareFitness['max_allocation_time']
    centralityAwareResponseTime = centralityAwareFitness['estimated_latency']

    return centralityAwareOptimizationTime,centralityAwareResponseTime
    



#******************************************************************************************
#   END Control cases (cloud, centralities)
#******************************************************************************************






#******************************************************************************************
#   Objectives and fitness calculation
#******************************************************************************************





def get_allocation_time(times):
    return max(times.values())


def closestDevice4DeployedAppInColony(idColony,idApp,idSourceDev,placementMatrix):
    distance = float('inf') #inicialmente consideramos que el timpo hasta el lugar donde esta la app placed es infinito
    placedInColony = False
    closestDevice = -1
    
    
    for id_dev in GAstructure4partition[idColony]['Cxi']:#busco todos los devices de la colonia donde esta la app
        if placementMatrix[idApp][id_dev] == 1:
            placedInColony = True
            if Gdistances[idSourceDev][id_dev] < distance:
                closestDevice = id_dev
                distance = Gdistances[idSourceDev][id_dev] #si esta en la colony, la distancia es la distancia directa entre los dos dispositivos

    return placedInColony, closestDevice


def estimated_latency_btw_users_and_services(colonies, node_services, cloud_services):
    
    accumulatedDistance = 0
    numApps = 0
    
    selectedColonies = list()
    for idx,colony in enumerate(colonies): #selecciono todas las colonias activas
        if colony==1:
            selectedColonies.append(idx)
            
    for idColony in selectedColonies:
        devicesInColony = GAstructure4partition[idColony]['Cxi']
        usersInColony = list()
        for user in domainConfiguration.myUsers:
            if user['id_resource'] in devicesInColony:
                usersInColony.append(user)
                
                
        for app in usersInColony: #recorro todas las apps que son solicitadas desde la colonia
            distance = float('inf') #inicialmente consideramos que el timpo hasta el lugar donde esta la app placed es infinito
            idApp = int(app['app'])
            idSourceNode = app['id_resource']
            placedInColony,idPlacingDev = closestDevice4DeployedAppInColony(idColony,idApp,idSourceNode,node_services) #miramos si en la own colony esta emplazada la app de esta iteración
            if placedInColony: #si esta emplazada, el tiempo de respuesta es la distsancia entre el nodo del usuario y el nodo que emplaza la app
                distance = Gdistances[idSourceNode][idPlacingDev] 
            else: #si no esta emplazada, hemos de buscar la colonia que tiene la app y que este mas cerca, y si esta esta mas cerca que el cloud o no
                coodinatorSourceColony=GAstructure4partition[idColony]['coordinator']  
                closestNeighbourd = domainConfiguration.cloudId
                closestCloud = True
                closestPlacingDevice = -1
                distance = g_distances_with_cloud[coodinatorSourceColony][domainConfiguration.cloudId] # el limite superior (peor caso) es que este en el cloud
                for idNeighbourdColony in selectedColonies: #recorremos todas las colonies que estan sleccionadas, y comprobamos que no sea la own colony
                    if idNeighbourdColony != idColony:
                        colonyCoordinatorNode = GAstructure4partition[idNeighbourdColony]['coordinator']
                        placedInColony,idPlacingDev = closestDevice4DeployedAppInColony(idNeighbourdColony,idApp,colonyCoordinatorNode,node_services)
                        if placedInColony: #si la neighbourd colony actual tiene la app y la distancia entre coordinadorees es menor que entre coordinador y cloud, o match acutal, lo sustituimos
                            tmp_intraColonyDistance =  Gdistances[coodinatorSourceColony][colonyCoordinatorNode]
                            if tmp_intraColonyDistance < distance:
                                distance = tmp_intraColonyDistance
                                closestCloud = False
                                closestNeighbourd = idNeighbourdColony
                                closestPlacingDevice = idPlacingDev
                                
                if closestCloud: #si el mas cercano resulta ser el cloud, a la distancia coordinator-cloud solo hay que sumarle la distancia user-coordinator
                    distance += Gdistances[idSourceNode][coodinatorSourceColony]
                else: # si el mas cercano es otra colony, a la distancia coordinator-coordinator hay que sumar las distancias user-coordinator y coordinator-placingDevice
                    distance += Gdistances[idSourceNode][coodinatorSourceColony]
                    distance += Gdistances[GAstructure4partition[closestNeighbourd]['coordinator']][closestPlacingDevice]
                                
            accumulatedDistance += distance
            numApps += 1
            
    return float(float(accumulatedDistance) / float(numApps))
            
def calculateFitnessObjectives(chromosome_col,chromosome_serv,chromosome_cloud_serv,chromosome_time, ocuped_nodes_resources):

    if str(chromosome_col) in calculated_fitness:
        return calculated_fitness[str(chromosome_col)]
    else:
        if ILP_METHOD:
            return calculateFitnessObjectivesILP(chromosome_col,chromosome_serv,chromosome_cloud_serv,chromosome_time, ocuped_nodes_resources)
        else:
            return calculateFitnessObjectivesGreedy(chromosome_col,chromosome_serv,chromosome_cloud_serv,chromosome_time)

def calculateFitnessObjectivesGreedy(chromosome_col,chromosome_serv,chromosome_cloud_serv,chromosome_time):
    chr_fitness = {}
    if checkConstraints(chromosome_col,chromosome_time):
        # cambiar el tiempo maximo por el tiempo medio

        chr_fitness["max_allocation_time"] = get_allocation_time(chromosome_time)
        chr_fitness["estimated_latency"] = estimated_latency_btw_users_and_services(chromosome_col,chromosome_serv,chromosome_cloud_serv)

        if ACTUAL_GENERATION:
            SCATTER_X.append(chr_fitness["max_allocation_time"])
            SCATTER_Y.append(chr_fitness["estimated_latency"])

        a = 0.5
        b = 0.5

        chr_fitness["total"] =  chr_fitness["max_allocation_time"] * a + chr_fitness["estimated_latency"] * b

    else:
        # print("not constraints")
        chr_fitness["max_allocation_time"] = float('inf')
        chr_fitness["estimated_latency"] = float('inf')
        chr_fitness["total"] = float('inf')

    calculated_fitness[str(chromosome_col)] = chr_fitness
    return chr_fitness

def mean_colonies_free_resources(colonies, ocuped_nodes_resources):
    colonies_idx = [n for n,i in enumerate(colonies) if i == 1]
    free_resources = [0]*len(colonies_idx)
    for n,colonie in enumerate(colonies_idx):
        colonie_nodes = GAstructure4partition[colonie]["Cxi"]
        for node in colonie_nodes:
            free_resources[n] += (domainConfiguration.nodeResources[node] - ocuped_nodes_resources[node])
    
    # mean
    result = sum(free_resources) / len(free_resources)
    return result


def calculateFitnessObjectivesILP(chromosome_col,chromosome_serv,chromosome_cloud_serv,chromosome_time,ocuped_nodes_resources):
    # Para la nueva funcion de fitness del GA hacer la media SUMATORIO ( recursos libres en cada colonia / num colonias )
    # como recursos libres entiendo la suma de los recursos libres de cada nodo de la colonia o simplemente 
    # contar lo nodos que no alojan ninguna app?????
    chr_fitness = {}
    if checkConstraints(chromosome_col,chromosome_time):
        chr_fitness["max_allocation_time"] = get_allocation_time(chromosome_time)
        chr_fitness["free_resources"] = mean_colonies_free_resources(chromosome_col, ocuped_nodes_resources)

        if ACTUAL_GENERATION:
            SCATTER_X.append(chr_fitness["max_allocation_time"])
            SCATTER_Y.append(chr_fitness["free_resources"])

        a = 0.5
        b = 0.5

        chr_fitness["total"] =  chr_fitness["max_allocation_time"] * a + chr_fitness["free_resources"] * b

    else:
        # print("not constraints")
        chr_fitness["max_allocation_time"] = float('inf')
        chr_fitness["free_resources"] = float('inf')
        chr_fitness["total"] = float('inf')

    calculated_fitness[str(chromosome_col)] = chr_fitness
    return chr_fitness



#******************************************************************************************
#   END Objectives and fitness calculation
#******************************************************************************************



#******************************************************************************************
#   NSGA-II Algorithm
#******************************************************************************************

def dominates(a,b):
    #checks if solution a dominates solution b, i.e. all the objectives are better in A than in B
    Adominates = True

    equalValues = True
    for key in a:
        if key in objectivesKeys:
            if b[key]!=a[key]:
                equalValues = False
                break
    if equalValues:
        return False

    for key in a:
        if key in objectivesKeys:  
            if b[key]<a[key]:
                Adominates = False
                break
    return Adominates



def crowdingDistancesAssigments(pop,numFront):

    front = pop["fronts"][numFront]


    frontFitness = list()
    for i in front:
        frontFitness.append(pop["fitness"][i])
        frontFitness[-1]["index"]=i

    for key in objectivesKeys:
        orderedList = sorted(frontFitness, key=lambda k: k[key])

        pop["crowdingDistance"][orderedList[0]["index"]] = float('inf')
        minObj = orderedList[0][key]
        pop["crowdingDistance"][orderedList[-1]["index"]] = float('inf')
        maxObj = orderedList[-1][key]

        normalizedDenominator = float(maxObj-minObj)
        if normalizedDenominator==0.0:
            normalizedDenominator = float('inf')

        for i in range(1, len(orderedList)-1):
            if orderedList[i]["index"]==8:
                printlog("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@",5)
                printlog(key,5)
                printlog(orderedList[i+1]["index"],5)
                printlog(orderedList[i+1][key],5)
                printlog(orderedList[i-1]["index"],5)
                printlog(orderedList[i-1][key],5)
                printlog(normalizedDenominator,5)
                printlog("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@",5)
            #anyado esto para evitar si me encuentro con valores iguales que no produzca el fallo del final
            if (orderedList[i+1][key]==orderedList[i][key]):
                pop["crowdingDistance"][orderedList[i]["index"]]=0.0
            elif (orderedList[i-1][key]==orderedList[i][key]):
                pop["crowdingDistance"][orderedList[i]["index"]]=0.0
            else:
                pop["crowdingDistance"][orderedList[i]["index"]] += (orderedList[i+1][key] - orderedList[i-1][key])/normalizedDenominator
            #con solo esta linea, si los valores de fitness son iguales para tres puntos, uno se queda con crwodingdistance = 0.0 y los otros dos con la resta al de un solo lado.
            #pop["crowdingDistance"][orderedList[i]["index"]] += (orderedList[i+1][key] - orderedList[i-1][key])/normalizedDenominator

def calculateCrowdingDistances(pop):

    pop["crowdingDistance"] = list()

    for i in pop["Col"]:
        pop["crowdingDistance"].append(float(0))

    i=0
    while len(pop["fronts"][i])!=0:
        crowdingDistancesAssigments(pop,i)
        i+=1


def calculateDominants(pop):

    pop["dominatedBy"] = list()
    pop["dominatesTo"] = list()
    pop["fronts"] = list()

    for i in range(len(pop["Col"])):
        pop["dominatedBy"].append(set())
        pop["dominatesTo"].append(set())
        pop["fronts"].append(set())

    for p in range(len(pop["Col"])):
        for q in range(p+1,len(pop["Col"])):
            if dominates(pop["fitness"][p],pop["fitness"][q]):
                pop["dominatesTo"][p].add(q)
                pop["dominatedBy"][q].add(p)
            if dominates(pop["fitness"][q],pop["fitness"][p]):
                pop["dominatedBy"][p].add(q)
                pop["dominatesTo"][q].add(p)

def calculateFronts(pop):

    addedToFronts = set()

    tempDominitedBy = copy.deepcopy(pop["dominatedBy"])


    i=0
    while len(addedToFronts)<len(pop["Col"]):
        pop["fronts"][i] = set([index for index,item in enumerate(tempDominitedBy) if item==set()])
        addedToFronts = addedToFronts | pop["fronts"][i]

        for index,item in enumerate(tempDominitedBy):
            if index in pop["fronts"][i]:
                tempDominitedBy[index].add(-1)
            else:
                tempDominitedBy[index] = tempDominitedBy[index] - pop["fronts"][i]
        i+=1


    pop["inFront"] = list()
    for i in pop["Col"]:
        pop["inFront"].append(-1)

    for i,v in enumerate(pop["fronts"]):
        for j in v:
            pop["inFront"][j]=i

def fastNonDominatedSort(pop):

    calculateDominants(pop)
    calculateFronts(pop)
    calculateCrowdingDistances(pop)


def splitPopsByDominance(joinPop):
    newpop = {}
    idsNewPop = set()

    popSize=0
    totalFronts = len(joinPop['fronts'])

    for i in range(totalFronts):
        elementsInFront = len(joinPop['fronts'][i])
        if (popSize + elementsInFront) <= populationSize:
            popSize = popSize + elementsInFront
            idsNewPop = idsNewPop | joinPop['fronts'][i]  #union of the current ids and all the ones in the current front
        else:

            solWithCrowDist = {}
            for solId in  joinPop['fronts'][i]:
                solWithCrowDist[solId]=joinPop['crowdingDistance'][solId]
            orderedByCD = [k for k, v in sorted(solWithCrowDist.items(), key=lambda item: item[1], reverse=True)]
            selectedOnes =set(orderedByCD[0:(populationSize-popSize)])
            idsNewPop = idsNewPop | selectedOnes
            break


    newpop['Col'] = list()
    newpop['Serv'] = list()
    newpop['Cloud']=list()
    newpop['fitness'] = list()

    for i in idsNewPop:
        newpop['Col'].append(joinPop['Col'][i])
        newpop['Serv'].append(joinPop['Serv'][i])
        newpop['Cloud'].append(joinPop['Cloud'][i])
        newpop['fitness'].append(joinPop['fitness'][i])


    return newpop


#******************************************************************************************
#   END NSGA-II Algorithm
#******************************************************************************************




def generateStructure(depth, partitionIterator, previousState,partitionStructure):

    depth = depth +1
    currentState = partitionIterator.next()
    differentSets = list()
    differentIds = list()
    for i,v in enumerate(currentState):
        if (v not in previousState):
            differentSets.append(v)
            differentIds.append(i)
    if len(differentSets) > 2:
        print("ERRRRORRRRRRRRR")

    previousSet = differentSets[0] | differentSets[1]
    previousSetId = previousState.index(previousSet)


    for j in range(0,2):
        if len(differentSets[j])>0:
        #if len(differentSets[j])>1:
            newSet = {}
            newSet['Cxi']= differentSets[j]
            tempset = set()
            tempset.add(len(partitionStructure))
            Axi = partitionStructure[previousSetId]['Axi'] | tempset
            newSet['Axi']= Axi
            newSet['detph']=depth
            partitionStructure.append(newSet)



def getMaxCentrality(centralities, setNodes):


    selectedNode = list(setNodes)[0]
    maxCentrality=centralities[selectedNode]

    for i in setNodes:
        if centralities[i]>maxCentrality:
            maxCentrality = centralities[i]
            selectedNode = i

    return selectedNode


def deviceDistances(GRAPH):
    dist_ = nx.shortest_path_length(GRAPH)
    distances = {}

    for i in dist_:
        distances[i[0]]=i[1]

    return distances


def meanCell2ControllerDistance(controller,cellSet):

    distance = 0.0
    elements = 0
    for i in cellSet:
        elements = elements + 1
        distance = Gdistances[controller][i] + distance

    meanDistance = distance / elements
    return meanDistance



def dendrogramCalculation(GRAPH):

    timecom = time.time()
    print("Calculating the communities....")
    communities_generator = community.girvan_newman(GRAPH)
    clustMeasure = nx.betweenness_centrality(GRAPH)
#    sorted_clustMeasure = sorted(clustMeasure.items(), key=operator.itemgetter(1),reverse=True)
    print("Communities calculated in "+str(time.time()-timecom))
    #calculamos la particion el grafo


    previousState = list()
    previousState.append(set(GRAPH.nodes))
    previousState = tuple(previousState)
    partitionStructure = list()

    depth = 0
    newSet = {}
    newSet['Cxi']= set(GRAPH.nodes)
    centralNode = getMaxCentrality(clustMeasure,newSet['Cxi'])
    newSet['coordinator']=centralNode
    Axi = set()
    Axi.add(0)
    newSet['Axi']= Axi
    newSet['depth']=depth
    newSet['cell2controllerDistance']=meanCell2ControllerDistance(centralNode,set(GRAPH.nodes))
    partitionStructure.append(newSet)
    #introducimos el primer elemento en la estrcutura resultante
    #es decir, el que cuyo camino previo Cxi es la primera bifurcacion del dendograma "0"
    #y el conjunto de elementos son todos ellos


    partitionIterator = itertools.islice(communities_generator, GRAPH.number_of_nodes())

    #avanzamos en la iteracion del todo los niveles del dendograma
    for currentState in partitionIterator:
        depth = depth +1
        #incrementamos la profundidad/nivel del dendograma
        differentSets = list()
        differentIds = list()
        #buscamos los dos nuevos conjuntos de elementos que no estaban en la iteracion anterior
        #es decir, son los dos nuevos comunities obtenidos
        for i,v in enumerate(currentState):
            if (v not in previousState):
                differentSets.append(v)
                differentIds.append(i)

        #si hay mas de dos, es que hay algun error
        if len(differentSets) > 2:
            print("ERRRRORRRRRRRRR")

        #generamos el community del que se han obtenido los dos nuevos y lo buscamos el id
        #de dicho community con el for que hay
        previousSet = differentSets[0] | differentSets[1]


        previousSetId= -1
        for ii,vv in enumerate(partitionStructure):
            if previousSet == vv['Cxi']:
                previousSetId = ii


        #una vez que sabemos los dos nuevos communities, y el community del que provienen
        #podemos incluir los dos nuevos en la estructura resultante partitionStructure
        #complentado la informacion del Cxi -que son los elementos que hay ene l community-
        #y el path hasta la cima del dendograma, que se construye anyadiendo el id de la nueva
        #bifurcacion al path que tenia el community del que proviene
        for j in range(0,2):
            #solo anyadios los nuevos communities que son division de communities. si es un community
            #de un elemento este nunca se dividira y por tanto no lo incluimos
            if len(differentSets[j])>0:
            #if len(differentSets[j])>1:
                newSet = {}
                newSet['Cxi']= differentSets[j]
                centralNode = getMaxCentrality(clustMeasure,newSet['Cxi'])
                newSet['coordinator']=centralNode
                tempset = set()
                tempset.add(len(partitionStructure))
                Axi = partitionStructure[previousSetId]['Axi'] | tempset
                newSet['Axi']= Axi
                newSet['depth']=depth
                newSet['cell2controllerDistance']=meanCell2ControllerDistance(centralNode,differentSets[j])
                partitionStructure.append(newSet)

        #actualizamos el depth del community padre para saber en que nivel se ha dividido
        partitionStructure[previousSetId]['depth']=depth-1


        previousState = currentState

    return partitionStructure


## Ordena los nodos de cada colonia de menor a mayor distancia al nodo coordinador
def oderNodesInColony(partitionStructure):
     orderedNodes = list()

     for colony in partitionStructure:
         distanceToCoordinator = {}
         coordinator = colony['coordinator']
         for node in colony['Cxi']:
             distanceToCoordinator[node]=Gdistances[coordinator][node]
         ordered = [k for k, v in sorted(distanceToCoordinator.items(), key=lambda item: item[1])]
         orderedNodes.append(ordered)
     return orderedNodes




## Devuelve una lista de listas, cada una de estas listas contiene para la colonia en cuestion
## el numero de servicios de cada aplicacion ??
def getNumUserService4Colonies(partitionStructure):
     numUserService = list()

     for colony in partitionStructure:
         numServ = list()
         numServ = [0 for s in range(domainConfiguration.TOTALNUMBEROFAPPS)]
         for node in colony['Cxi']:
             for user in domainConfiguration.myUsers:
                 if node==user['id_resource']:
                     serv = int(user['app'])
                     numServ[serv]=numServ[serv]+1
         numUserService.append(numServ)
     return numUserService


## Ordena las listas de cada colonia segun app popularity
## (no se muy bien como, que criterio esta siguiemdo)
def orderAppsPopularityInColony(userService4Colonies):

    orderedAppPopularity = list()
    ordered_app_popularity_list = list()

    for numApps in userService4Colonies:
        sortedApps = numpy.argsort(numApps)[::-1]
        orderedAppPopularity.append(sortedApps)
        ordered_app_popularity_list.append(sortedApps.tolist())
    return orderedAppPopularity, ordered_app_popularity_list

def getRequestedServices4Colonies(partitionStructure):
    rqServ = list()

    for colony in partitionStructure:
        services = set()
        for node in colony['Cxi']:
            for user in domainConfiguration.myUsers:
                if node==user['id_resource']:
                    services.add(int(user['app']))
        rqServ.append(services)
    return rqServ



#******************************************************************************************
#   Repair operators
#******************************************************************************************




def repairSolution2LessColonies(sol,struc):    #dib
#ponemos a 0 todos los descendientes
    for i,v in enumerate(sol):
        if v==1:
        #al encontrar un 1 en la solucion que indica que la colony esta formada por todos los nodos
        # terminales que cuelgan desde ese nodo intermedio, se buscan todos los nodos hijos -son
        #aquellos que comparten la ruta de nodo predecesores.

            for j,w in enumerate(struc):
                if (len(w['Axi']) > len(struc[i]['Axi']) ) and (len(struc[i]['Axi'] - w['Axi']) == 0):
                    sol[j]=0

def repairSolution2MoreColonies(sol,struc):    #dib
#ponemos a 0 todos los predecesores

    for i,v in enumerate(sol):
        #al encontrar un 1 en la solucion que indica que la colony esta formada por todos los nodos
        # terminales que cuelgan desde ese nodo intermedio, se pone a 0 a todos los nodos padres
        if v==1:
            for j in struc[i]['Axi']:
                if not j==i:
                    sol[j]=0

def repairAllInColoniesMore(sol,struc): #dib
    #Busca todos los devices que no estan en un colony, y crea un colony de un unico dispositivo con dicho device

    nodesIncluded = set()
    for i,v in enumerate(sol):
        if v == 1:
            nodesIncluded = nodesIncluded | struc[i]['Cxi']

    for i,v in enumerate(struc):
        if len(v['Cxi'])==1 and len(v['Cxi'] & nodesIncluded)==0:
            sol[i]=1

def repairAllInColoniesLess(sol,struc): #dib
      #Busca el menor numero de colonies para incorporar todos los devices que quedan sin asociar a ningun colony
    nodesIncluded = set()
    for i,v in enumerate(sol): #miro todos los nodos que estan actualmente en una colonia
        if v == 1:
            nodesIncluded = nodesIncluded | struc[i]['Cxi'] 

    pendingNodes = allNodes - nodesIncluded  #obtengo los nodos que falta por incluir en colonias
    colonySize = dict()
    for i,v in enumerate(struc): #calculo el tamanyo de cada colony
        colonySize[i]=len(v['Cxi'])
        
    sortedColonySize = sorted(colonySize.items(), key=operator.itemgetter(1), reverse=True) #ordeno los colonies de mayor a menor por su tamanyo

    for i in sortedColonySize:
        idColony = i[0]
        if len(struc[idColony]['Cxi']-pendingNodes)==0: #si encuentro un proposed colony, que solo contenga nodos pendientes, lo selecciono. al estar ordenados de mayor tamanyo a menor, garantizo que los que obtenga seran los colonies mas grande y por tant la menor cantidad de colonies
            #print("seleccionada colony:"+str(idColony))
            sol[idColony]=1
            pendingNodes = pendingNodes - struc[idColony]['Cxi']
            #print("He juntado los nodos "+str(struc[idColony]['Cxi'])+" y ahora quedan los nodos: "+str(pendingNodes))
            #print("Aun quedan por colocar: "+str(len(pendingNodes)))
        #else:
            #print("descartar colony:"+str(idColony))                  
            


def repairAllInColonies(sol,struc,repairType): #dib
    printlog("repairAllinColonies",2)
    if repairType=='more':
        repairAllInColoniesMore(sol,struc)
        printlog("repairAllinColonies",2)
    if repairType=='less':
        repairAllInColoniesLess(sol,struc)
        printlog("less",2)

def repairSolution(sol,struc,repairType):   #dib

    printlog("repair",2)
    if repairType=='more':
        repairSolution2MoreColonies(sol,struc)
        printlog("more",2)
    if repairType=='less':
        repairSolution2LessColonies(sol,struc)
        printlog("less",2)
    repairAllInColonies(sol,struc,repairType)



#******************************************************************************************
#   END Repair operators
#******************************************************************************************



#******************************************************************************************
#   Crossover operators
#******************************************************************************************



def crossoverCol(sol1,sol2,struc):

    c1 = copy.copy(sol1)
    c2 = copy.copy(sol2)


    theones1=list()
    for i,v in enumerate(sol1):
        if v==1:
            theones1.append(i)

    theones2=list()
    for i,v in enumerate(sol2):
        if v==1:
            theones2.append(i)

    if random.random()>0.5:
        theones1,theones2 = theones2,theones1

    if len(theones1)>1:
        cutpoint = theones1[random.randint(0,len(theones1)-1)]
    elif len(theones2)>1:
        cutpoint = theones2[random.randint(0,len(theones2)-1)]
    else:
        cutpoint = random.randint(0,len(sol1)-1)


    precedence = struc[cutpoint]['Axi']
    genes2Change = set()
    for j,w in enumerate(struc):
        if (len(w['Axi']) > len(precedence) ) and (len(precedence - w['Axi']) == 0):
            genes2Change.add(j)

    genes2Change.add(cutpoint)

    for i in genes2Change:
        c1[i],c2[i]=c2[i],c1[i]

    repairSolution(c1,struc,'less')
    repairSolution(c2,struc,'less')

    return c1,c2



#******************************************************************************************
#   END Crossover operators
#******************************************************************************************



#******************************************************************************************
#   Mutation operators
#******************************************************************************************




def splitColony(sol,idColony,struc):

    precedence = struc[idColony]['Axi']
    foundAny = False
    for j,w in enumerate(struc):
        if (len(w['Axi'])-1 == len(precedence) ) and (len(precedence - w['Axi']) == 0):
            sol[j]=1
            foundAny = True
    if foundAny:
        sol[idColony]=0



def mutationSplitAll(sol,struc):

    theones=list()
    for i,v in enumerate(sol):
        if v==1:
            theones.append(i)
    for i in theones:
        splitColony(sol,i,struc)

def mutationSplitOne(sol,struc):
    printlog("SPLIT MUTATION",2)
    theones=list()
    for i,v in enumerate(sol):
        if v==1:
            theones.append(i)
    idColony2Split = theones[random.randint(0,len(theones)-1)]
    splitColony(sol,idColony2Split,struc)


def joinColony(sol,idColony,struc):

    myself = set()
    myself.add(idColony)
    set2Find = struc[idColony]['Axi'] - myself
    for j,w in enumerate(struc):
        if (w['Axi'] == set2Find ):
            sol[j]=1

    repairSolution(sol,struc,'less')


def mutationJoinAll(sol,struc):

    theones=list()
    for i,v in enumerate(sol):
        if v==1:
            theones.append(i)
    for i in theones:
        joinColony(sol,i,struc)


def mutationJoinOne(sol,struc):
    printlog("JOIN MUTATION",2)
    theones=list()
    for i,v in enumerate(sol):
        if v==1:
            theones.append(i)
    idColony2Join = theones[random.randint(0,len(theones)-1)]
    joinColony(sol,idColony2Join,struc)


def mutationAtomize(sol,struc):
    printlog("ATOMIZE MUTATION",2)

    idColony = random.randint(0,len(sol)-1)
    if sol[idColony]==0:
        sol[idColony]=1
    else:
        sol[idColony]=0

    repairSolution(sol,struc,'more')



def changeValueNode(sol,value):

    i = random.randint(0,domainConfiguration.TOTALNUMBEROFNODES-1)

    for idServ in range(0,domainConfiguration.TOTALNUMBEROFAPPS):
        sol[idServ][i]=value

def mutationFreeNode(sol):
    changeValueNode(sol,0)

def mutationFillNode(sol):
    changeValueNode(sol,1)

def mutationSwapNode(sol):

    tmp = list(range(0,domainConfiguration.TOTALNUMBEROFNODES))
    random.shuffle(tmp)

    i=tmp[0]
    j=tmp[1]

    for idServ in range(0,domainConfiguration.TOTALNUMBEROFAPPS):
        sol[idServ][i],sol[idServ][j]=sol[idServ][j],sol[idServ][i]


def mutate(solCol,struc):

    mutationOperators = []
#    mutationOperators.append(mutationSplitOne)
#    mutationOperators.append(mutationSplitAll)
    mutationOperators.append(mutationJoinOne)
#    mutationOperators.append(mutationJoinAll)
#    mutationOperators.append(mutationAtomize)
    mutationOperators[random.randint(0,len(mutationOperators)-1)](solCol,struc)




    
    
    
#******************************************************************************************
#   END Mutation operators
#******************************************************************************************


    
    
    
def createPopulationCol(repeat):
    popCol = list()


    i =0
    while len(popCol) < populationSize:
        printlog("AHORA TENGO############",2)
        printlog(len(popCol),2)
        printlog(populationSize,2)
        printlog("###################",2)
        i = i+1
        solution  = [random.randint(0,1) for element in range(len(GAstructure4partition))]
        if random.random()>0.5:
            repairSolution(solution,GAstructure4partition,'less')
        else:
            repairSolution(solution,GAstructure4partition,'more')
        printlog(solution,3)

        if repeat:
            popCol.append(solution)
        else:
            if (solution not in popCol):
                popCol.append(solution)

    printlog("AHORA TENGO############",2)
    printlog(len(popCol),2)
    printlog(populationSize,2)
    printlog("###################",2)
    return popCol




def createPopulation():

    pop = {}
    c=createPopulationCol(repeat=repeatedSolutions)
    s = list()
    ac = list()

    times = list() # NOTE:X
    free_resources = list() # NOTE:X

    for solCol in c:
        solServ,solCloud,solTimes,solFreeResources = allocateServicesInColonies(solCol)
        s.append(solServ)
        ac.append(solCloud)
        times.append(solTimes) # NOTE:X
        free_resources.append(solFreeResources) # NOTE:X

    pop["Col"] = c
    pop["Serv"] = s
    pop["Cloud"] = ac
    pop["fitness"] = list()
    for i in range(len(pop["Col"])):
        pop["fitness"].append(calculateFitnessObjectives(pop["Col"][i],pop["Serv"][i], pop["Cloud"][i], times[i], free_resources[i]))

    return pop

def tournamentSelection(pop,fi, fj):


    printlog(pop["inFront"],2)
    if pop["inFront"][fi]<pop["inFront"][fj]:
        printlog("Mejor front1",2)
        return fi
    if pop["inFront"][fi]>pop["inFront"][fj]:
        printlog("Mejor front2",2)
        return fj
    if pop["crowdingDistance"][fi]>pop["crowdingDistance"][fj]:
        printlog("Mejor distance1",2)
        return fi
    if pop["crowdingDistance"][fi]<pop["crowdingDistance"][fj]:
        printlog("Mejor distance2",2)
        return fj
    printlog("EERRROOOORRRRRRRRR##################### Igual front e igual distance",4)
    printlog(pop['Col'][fi],4)
    printlog(pop['fitness'][fi],4)
    printlog(pop['crowdingDistance'][fi],4)
    printlog(pop['Col'][fj],4)
    printlog(pop['fitness'][fj],4)
    printlog(pop['crowdingDistance'][fj],4)
    printlog(str(fi)+" "+str(fj),4)

    return random.choice([fi,fj])

def selectFathers(pop):

    s = [-1,-1]


    for i in range(2):
        fi = random.randint(0,populationSize-1)
        fj = random.randint(0,populationSize-1)
        while ((fj==fi) or (fj==s[0])):
            fj = random.randint(0,populationSize-1)

        s[i] = tournamentSelection(pop,fi,fj)


    return fi,fj


def order_colonies_by_coord_distance(colony_solution):
    # coger la posicion de los 1's, esos son los puntos del dendorgrama usados
    indices = [i for i, value in enumerate(colony_solution) if value == 1]
    #print(indices)
    colonies_ordered_by_distances = {}
    for i in indices:
        # vector de distancias iniciadas a -1 de la misma longitud que colony_solution
        distances = [-1 for n in range(len(colony_solution)+1)] # +1 per el cloud?
        for j in indices:
            # calcular la distancia del punto i respecto al resto de puntos que pertenecen a la colony solution
            distances[j] = (Gdistances[GAstructure4partition[i]["coordinator"]][GAstructure4partition[j]["coordinator"]])

        # afegir la distancia amb el cloud
        aux = distances[len(distances)-1] = g_distances_with_cloud[GAstructure4partition[i]["coordinator"]][domainConfiguration.cloudId]
        #distances[len(distances)-1] = 100

        # calcular el numero de distancias no validas (no pertenecen a la colony solution seleccioada)
        indx = sum(i<0 for i in distances)

        # meter en el diccionario, el vector de los indices ordenados, unicamente los indices validos (de las colonias pertenecientes a colony solution)
        colonies_ordered_by_distances[i]=(numpy.argsort(distances)[indx:]).tolist()

        # imp com gestionar "saber" si es el cloud (if i = len(colony_solution) ??)

    return colonies_ordered_by_distances


# definimos diccionario donde se guardaran los vectores de nodos ordenados por distancia a los usuarios
# que se hayan calculado
#nodes_by_distance_to_app_users = {}
# key: "C4N1,2,4,5,6"

def order_nodes_by_distance_to_app_users(my_colony, my_app):
    # guardamos todos los nodos de esta colonia
    nodes_in_colony = [node for node in GAstructure4partition[my_colony]["Cxi"]]
    # vector de nodos de la colonia donde solicitan la app
    nodes_of_colony_with_app = []
    # vector de id resources de la app
    app_id_resources = []

    # para cada app, si es la que estamos analizando, guardamos su id_resource
    for app in domainConfiguration.myUsers:
        if app["app"] == str(my_app):
            app_id_resources.append(app["id_resource"])

    # para cada cada nodo donde se solicita la app, miramos si pertenece a la colonia que estamos analizando, si es asi se mete en nodes_of_colony_with_app
    for colony in app_id_resources:
        nodes_of_colony_with_app.extend([node for node in GAstructure4partition[colony]["Cxi"] if node in nodes_in_colony and node not in nodes_of_colony_with_app])

    # eliminar duplicados (no deberia haber)
    #nodes_of_colony_with_app = list(set(nodes_of_colony_with_app))

    # ordenar la lista
    nodes_of_colony_with_app.sort()
    # mirar si ya tengo esa combinacion de colonia y nodos calculada y guardada
    key = "C"+str(my_colony)+"N"+(','.join([str(node) for node in nodes_of_colony_with_app]))

    if key in nodes_by_distance_to_app_users:
        return nodes_by_distance_to_app_users[key]

    else:
        # si no la tengo guardada, calcularla
        # para cada nodo de la colonia, calcular la distancia entre el y todos los nodos donde esta la app y hacer la media
        distances = {}
        for node in nodes_in_colony:
            acum = 0

            for app_node in nodes_of_colony_with_app:
                acum += Gdistances[node][app_node]

            distance = acum / len(nodes_of_colony_with_app) if acum != 0 else 0

            distances[node] = distance

        # ordenar el diccioario por valores y coger solo las keys, que son los nodos
        ordered_nodes = sorted(distances, key=distances.get)

        # guardarlo en el diccionario
        nodes_by_distance_to_app_users[key] = ordered_nodes

        return ordered_nodes

def is_app_in_colonie(my_colony, my_app, allocation):
    # guardamos todos los nodos de esta colonia
    nodes_in_colony = [node for node in GAstructure4partition[my_colony]["Cxi"]]

    # comprovamos si la app ya esta colocada en alguno de los nodos
    for idNode in nodes_in_colony:
        if allocation[my_app][idNode]==1:
            return True
    
    return False


        
        

#******************************************************************************************
#   Service allocation algorithms
#******************************************************************************************

        

def allocateServicesInColonies(colony_solution):
    if str(colony_solution) in allocated_services:
        return allocated_services[str(colony_solution)]
    else:
        if ILP_METHOD:
            return allocateServicesInColoniesILP3(colony_solution)
        else:
            return allocateServicesInColoniesNormalFinal(colony_solution)
def allocateServicesInColoniesNormalFinal(colonySolution):
    global_start = time.time()
    # version final, implementant posar la app al node amb menor distancia.
    # alhora de mirar si la colonia a la que li mand es el cloud, haure de fer (if i == len(colonySolution))
    colonies_ordered_by_distances = order_colonies_by_coord_distance(colonySolution)

    allocation = [[0 for node in range(domainConfiguration.TOTALNUMBEROFNODES)] for serv in range(domainConfiguration.TOTALNUMBEROFAPPS)]
    allocCloud = [0 for serv in range(domainConfiguration.TOTALNUMBEROFAPPS)]
    allocatedResources = [0 for node in range(domainConfiguration.TOTALNUMBEROFNODES)]

    times = {}
    for colonie in colonies_ordered_by_distances.keys():
        times[colonie]=0

    processing_colonies = True
    colonies_dict_indx = 0
    #pending_apps_ordered_by_popularity = copy.deepcopy(orderedAppPopularity4Colonies)
    pending_apps_ordered_by_popularity = copy.deepcopy(ordered_app_popularity_4colonies_list) # !!

    print_x("empezamos")

    while processing_colonies:
        # tiempo de inicio
        start = time.time()
        colonie_indx = list(colonies_ordered_by_distances.keys())[colonies_dict_indx]

        print_x("Lista colonias:")
        print_x(colonies_ordered_by_distances)
        print_x("procesando colonia: %i"%colonie_indx)

        trying_colonie_indx = list(colonies_ordered_by_distances.values())[colonies_dict_indx].pop(0)

        apps_to_remove = []

        for idApp in pending_apps_ordered_by_popularity[colonie_indx]: # loop por cada app de la colonia, ordenadas por popularidad
            print_x("pending apps:")
            print_x(pending_apps_ordered_by_popularity[colonie_indx])
            print_x("actual app")
            print_x(idApp)

            print_x("num4serv")
            print_x(numUserService4Colonies[colonie_indx])

            if numUserService4Colonies[colonie_indx][idApp]<=0:
                # no se accede a esta app, no se quiere colocar y se elimina de pendientes.
                print_x("no accedo a esta app, la borrare")
                apps_to_remove.append(idApp)

            else:# si el num de accesos a la app es >=1
                if trying_colonie_indx == len(colonySolution): # si la app se esta intentando poner en el cloud
                    # si no esta en el cloud la ponemos
                    if allocCloud[idApp]!=1:
                        # se manda al cloud
                        print_x("Te la mando pal cloud")
                        allocCloud[idApp]=1

                    # en cualquiera de los dos casos hay que eliminarla de pendientes
                    apps_to_remove.append(idApp)
                else:
                    print_x("no al cloud")
                    for idNode in order_nodes_by_distance_to_app_users(trying_colonie_indx, idApp):

                        ## hay q comprovar que no la app no se encuentre ya en un nodo de la community
                        ## hacer en este mimsmo bucle (no hace falta otro) pq el orden de nodos que miro sera el mismo para
                        ## todas las veces que quiera colocar una app en una comunity determinada

                        if allocation[idApp][idNode]==1: # la app ya esta colocada
                            print_x("ya estaba colocada")
                            ## no se si tengo que hacer alguna asignacion aqui
                            # eliminar la app de pendents
                            apps_to_remove.append(idApp)
                            break

                        elif (allocatedResources[idNode]+domainConfiguration.apps[idApp]['resources'])<=(domainConfiguration.nodeResources[idNode]):
                            print_x("la coloco en la colonia %i"%trying_colonie_indx)
                            # indicar que esa app se encuentra en ese nodo
                            allocation[idApp][idNode]=1
                            # augmentar el espacio ocupado del nodo
                            allocatedResources[idNode] = allocatedResources[idNode] + domainConfiguration.apps[idApp]['resources']

                            # eliminar la app de la lista de pendientes
                            apps_to_remove.append(idApp)
                            break
        # sumamos el tiempo
        times[colonie_indx]+=time.time()-start
        


        print_x("len antes de borrar")
        print_x(len(pending_apps_ordered_by_popularity[colonie_indx]))
        print_x("borro:")
        for i in apps_to_remove:
            print_x(i)
            pending_apps_ordered_by_popularity[colonie_indx].remove(i)

        print_x("len despues de borrar")
        print_x(pending_apps_ordered_by_popularity[colonie_indx])

        if len(pending_apps_ordered_by_popularity[colonie_indx]) == 0:
            # si en esa colonia ya no hay apps pendientes, se elimina la colonia de la lista de colonias
            del colonies_ordered_by_distances[colonie_indx]
            if colonies_dict_indx >= len(colonies_ordered_by_distances.keys()):
                # esto es pq si estoy procesando el ultimo y lo elimino, tendre que volver al primero
                # i si no hago esto, no vuelvo i se estara intentando acceder a una posicion que no existe
                colonies_dict_indx = 0
        else:
            # si no, se augmenta el indice, para realizar el proceso con la siguiente colonia
            colonies_dict_indx = (colonies_dict_indx + 1) % (len(colonies_ordered_by_distances.keys()))

        if len(colonies_ordered_by_distances.keys())==0:
            print_x("finito")
            processing_colonies = False


    for i,v in times.items():
        times[i]=v*scaleOptimizationTime


    #print(time.time()-global_start)
    allocated_services[str(colonySolution)] = allocation,allocCloud,times,None
    return allocation,allocCloud,times,None

def ilp_latency_and_lambda(app, node, colony):
    acum_users_values = 0
    acum_request_ratios = 0
    acum_lambda = 0

    req_nodes = []
    for user in domainConfiguration.myUsers:

        if int(user["app"]) == app and user["id_resource"] in GAstructure4partition[colony]["Cxi"]:
            req_nodes.append(user)
    
    for req_node in req_nodes:
        distance = Gdistances[req_node["id_resource"]][node]

        acum_users_values += distance * (1 / req_node['lambda'])
        # chequear este acum_req_ratios, aqui i en fitness
        acum_request_ratios += req_node['lambda']

        acum_lambda += 1/req_node['lambda']
    
    estimated_latency = acum_users_values / (1 / acum_request_ratios)
    acum_lambda = 1/acum_lambda
    return estimated_latency, acum_lambda

def get_free_resources_on_colonie(colonie_nodes, ocupation_list):
    nodes_resources = [0]*len(colonie_nodes)
    for idx, node in enumerate(colonie_nodes):
        nodes_resources[idx] = domainConfiguration.nodeResources[node] - ocupation_list[node]
    return nodes_resources

def allocateServicesInColoniesILP3(colony_solution):
    #global_start = time.time()
    ## Nuevo objetivo ILP (minimizar el numero de recursos no utilizados en cada colonia)
    ## minimizar num de recursos libres

    # with ilp
    colonies_ordered_by_distances = order_colonies_by_coord_distance(colony_solution)

    allocation = [[0 for node in range(domainConfiguration.TOTALNUMBEROFNODES)] for serv in range(domainConfiguration.TOTALNUMBEROFAPPS)]
    allocCloud = [0 for serv in range(domainConfiguration.TOTALNUMBEROFAPPS)]
    allocatedResources = [0 for node in range(domainConfiguration.TOTALNUMBEROFNODES)]

    #print(allocatedResources)
    #print(domainConfiguration.nodeResources)

    times = {}
    for colonie in colonies_ordered_by_distances.keys():
        times[colonie]=0

    processing_colonies = True
    colonies_dict_indx = 0

    #pending_apps_ordered_by_popularity = copy.deepcopy(ordered_app_popularity_4colonies_list) # !!
    
    # get all unique apps id
    #pending_apps_ids = list(dict.fromkeys(int(app["app"]) for app in domainConfiguration.myUsers))
    pending_apps_ids = []
    for colony in GAstructure4partition:
        pending_apps_ids.append(list(dict.fromkeys(int(app["app"]) for app in domainConfiguration.myUsers)))

    print_x("empezamos")

    while processing_colonies:
        # tiempo de inicio
        start = time.time()
        colonie_indx = list(colonies_ordered_by_distances.keys())[colonies_dict_indx]

        print_x("Lista colonias:")
        print_x(colonies_ordered_by_distances)
        print_x("procesando colonia: ", colonie_indx)

        trying_colonie_indx = list(colonies_ordered_by_distances.values())[colonies_dict_indx].pop(0)

        # miro si no se accede a ellas o se accede pero ya se encuentra en la colonia donde se intenta colocar
        # en esos casos las borro
        
        apps_to_delete = []

        for idApp in pending_apps_ids[colonie_indx]:
            if numUserService4Colonies[colonie_indx][idApp]<=0:
                # no se accede a esta app, no se quiere colocar y se elimina
                print_x("no accedo a esta app, la borro")
                apps_to_delete.append(idApp)
            
            elif trying_colonie_indx == len(colony_solution): # si las apps se estan intentando poner en el cloud
                if allocCloud[idApp]!=1:
                    # se manda al cloud
                    print_x("La mando cloud")
                    allocCloud[idApp]=1

                # en cualquiera de los dos casos hay que eliminarla de pendientes
                apps_to_delete.append(idApp)
                #print(pending_apps_ids[colonie_indx])
            
            elif is_app_in_colonie(trying_colonie_indx, idApp, allocation):
                print_x("ya esta en la colonia, la borro")
                apps_to_delete.append(idApp)
        
        # delete de "allocated" apps
        for app in apps_to_delete:
            pending_apps_ids[colonie_indx].remove(app)
        apps_to_delete = []
        
        
        # si llegados a este punto, el tamaño de la lista es > 0
        # querra decir que aun hay apps por colocar i no es en el cloud
        # en este punto es cuando hay que aplicar ilp
        
        if len(pending_apps_ids[colonie_indx]) > 0:
            #ilp 
            
            # create the ilp problem
            problem = pulp.LpProblem("ServicesAllocation",pulp.LpMaximize)
            
            nodes = list(GAstructure4partition[trying_colonie_indx]["Cxi"])
            apps = pending_apps_ids[colonie_indx]

            # variables 
            # my_vars = []
            # for column in apps:
            #     for row in nodes:
            #         my_vars.append("%i,%i"%(column,row))
            
            #trolling code
            my_vars = ["%i,%i"%(column,row) for column in apps for row in nodes]

            matrix_vars = pulp.LpVariable.dicts("Col,Row",my_vars, cat='Binary')
            
            # main objective, maximize allocated resources
            allocated_resources = {}
            for column in apps:
                for idx, row in enumerate(nodes):
                    allocated_resources["%i,%i"%(column,row)] = allocatedResources[idx]

            problem += pulp.lpSum([allocated_resources[i] * matrix_vars[i] for i in matrix_vars.keys()]), "Objective"
            

            # add constrains

            # dont allocate more apps than its capacity permits
            for row in nodes:
                problem += pulp.lpSum([(matrix_vars["%i,%i"%(column,row)] * domainConfiguration.apps[column]['resources']) for column in apps])<=(domainConfiguration.nodeResources[row] - allocatedResources[row]),("DeviceCapacity_%i"%row)

            # cada app, solo una vez en la misma colonia
            for column in apps:
                problem += pulp.lpSum([(matrix_vars["%i,%i"%(column,row)] ) for row in nodes]) <= 1 , 'LowerBound_' + str(column)
            
            problem.solve(pulp.PULP_CBC_CMD(msg=False))
            for variable in problem.variables():
                if variable.varValue:
                    col_row = str(variable).split("_")[-1]
                    var_app = int(col_row.split(",")[0])
                    var_node = int(col_row.split(",")[1])
                    
                    # indicar que la app se encuentra en el nodo
                    allocation[var_app][var_node]=1

                    # augmentar el espacio ocupado del nodo
                    allocatedResources[var_node] = allocatedResources[var_node] + domainConfiguration.apps[var_app]['resources']

                    # eliminar la app de la lista de pendientes
                    apps_to_delete.append(var_app)

            # delete de "allocated" apps
            for app in apps_to_delete:
                pending_apps_ids[colonie_indx].remove(app)

        # sumamos el tiempo
        times[colonie_indx]+=time.time()-start

        if len(pending_apps_ids[colonie_indx]) == 0:
            # si en esa colonia ya no hay apps pendientes, se elimina la colonia de la lista de colonias
            del colonies_ordered_by_distances[colonie_indx]
            if colonies_dict_indx >= len(colonies_ordered_by_distances.keys()):
                # esto es pq si estoy procesando el ultimo y lo elimino, tendre que volver al primero
                # i si no hago esto, no vuelvo i se estara intentando acceder a una posicion que no existe
                colonies_dict_indx = 0
        else:
            # si no, se augmenta el indice, para realizar el proceso con la siguiente colonia
            colonies_dict_indx = (colonies_dict_indx + 1) % (len(colonies_ordered_by_distances.keys()))

        if len(colonies_ordered_by_distances.keys())==0:
            print_x("finito")
            processing_colonies = False
    #print(time.time()-global_start)
    allocated_services[str(colony_solution)] = [allocation,allocCloud,times,allocatedResources]
    return allocation,allocCloud,times,allocatedResources




#******************************************************************************************
#   END Service allocation algorithms
#******************************************************************************************




def newGeneration(pop,repeat):

    offspring = {}
    offspring["Col"] = list()
    offspring["Serv"] = list()
    offspring["Cloud"] = list()
    offspring["fitness"] = list()

    ii=0
    while len(offspring["Col"]) < populationSize:

        fi,fj = selectFathers(pop)

        if random.random()<crossoverProb:

            ci,cj = crossoverCol(pop["Col"][fi],pop["Col"][fj],GAstructure4partition)
            printlog(ci,3)
            printlog(cj,3)

        else:
            ci = copy.deepcopy(pop["Col"][fi])
            cj = copy.deepcopy(pop["Col"][fj])




        if random.random()>mutationProb:
            mutate(ci,GAstructure4partition)
        if random.random()>mutationProb:
            mutate(cj,GAstructure4partition)


        si,aci,times_i,free_resources_i=allocateServicesInColonies(ci)
        sj,acj,times_j,free_resources_j=allocateServicesInColonies(cj)

        # repairServAlloc(si,ci,GAstructure4partition)
        # repairServAlloc(sj,cj,GAstructure4partition)

        printlog(ii,2)
        ii=ii+1

        if repeat:
            offspring["Col"].append(ci)
            offspring["Serv"].append(si)
            offspring["Cloud"].append(aci)
            offspring["fitness"].append(calculateFitnessObjectives(ci,si,aci,times_i,free_resources_i))
            printlog(ci,3)
            offspring["Col"].append(cj)
            offspring["Serv"].append(sj)
            offspring["Cloud"].append(acj)
            offspring["fitness"].append(calculateFitnessObjectives(cj,sj,acj,times_j,free_resources_j))
            printlog(cj,3)
        else:
            if (ci not in offspring["Col"]) and (ci not in pop["Col"]):
                offspring["Col"].append(ci)
                offspring["Serv"].append(si)
                offspring["Cloud"].append(aci)
                offspring["fitness"].append(calculateFitnessObjectives(ci,si,aci,times_i,free_resources_i))
                printlog(ci,3)
            if (cj not in offspring["Col"])  and (cj not in pop["Col"]):
                offspring["Col"].append(cj)
                offspring["Serv"].append(sj)
                offspring["Cloud"].append(acj)
                offspring["fitness"].append(calculateFitnessObjectives(cj,sj,acj,times_j,free_resources_j))
                printlog(cj,3)
        if ii > 500:
            printlog(offspring["Col"],4)
            print("ERROR, only an offspring of "+str(len(offspring["Col"]))+" solutions is generated.")
            break




    joinPop = {}

    joinPop["Col"] = pop["Col"] + offspring["Col"]
    joinPop["Serv"] = pop["Serv"] + offspring["Serv"]
    joinPop["Cloud"] = pop["Cloud"] + offspring["Cloud"]
    joinPop["fitness"] = pop["fitness"] + offspring["fitness"]

    return joinPop


def getMinMaxObjective(obj):

    myMax = 0.0
    myMin = float('inf')
    for i in pop['fronts'][0]:
        if pop['fitness'][i][obj]<myMin:
            myMin = pop['fitness'][i][obj]
        if pop['fitness'][i][obj]>myMax:
            myMax = pop['fitness'][i][obj]

    return myMin,myMax




#******************************************************************************************
#   Main loud execution experiments for different number of apps and nodes
#******************************************************************************************


radarLabels = list()
fsColonyOptTime = list()
oneColoyOptTime = list()
selectedFromParetoOptTime = list()
finalHyperVolume = list()
finalCoverage1CGA = list()
finalCoverageFSGA = list()
finalCoverageGA1C = list()
finalCoverageGAFS = list()

fsColonyNetTime = list()
oneColoyNetTime = list()
selectedFromParetoNetTime = list()



for oneExperiment in experiments2execute:
    appNumber = oneExperiment[0]
    nodeNumber = oneExperiment[1]


    print("#******************************************************************************************")
    print("#  "+str(appNumber)+" apps and "+str(nodeNumber)+" nodes")
    print("#******************************************************************************************")


    # definimos diccionario donde se guardaran los vectores de nodos ordenados por distancia a los usuarios
    # que se hayan calculado
    nodes_by_distance_to_app_users = {}
    # key: "C4N1,2,4,5,6"
    
    
    ALL_X_PLOT = []
    ALL_Y_PLOT = []
    
    ALL_SCATTERS_X = []
    ALL_SCATTERS_Y = []
    
    # guardar soluciones ya calculadas
    allocated_services = {}
    calculated_fitness = {}
    

    if ILP_METHOD:
        objectivesKeys = ["max_allocation_time","free_resources"]  #NECESARIO PARA FRENTES PARETOS, SIEMPRE TIENE QUE ESTAR ACTUALIZADO
    else:
        objectivesKeys = ["max_allocation_time","estimated_latency"]  #NECESARIO PARA FRENTES PARETOS, SIEMPRE TIENE QUE ESTAR ACTUALIZADO
    

    storageFoldershort="./plots2/"
    if not os.path.exists(storageFoldershort):
            os.mkdir(storageFoldershort)
    
    storageFolder = storageFoldershort+str(nodeNumber)+"nodes"+str(appNumber)+"apps/"
    if not os.path.exists(storageFolder):
            os.mkdir(storageFolder)
    
    domainConfiguration.initializeRandom(randomSeeds)
    domainConfiguration.setRandomState(randomSeeds)
    domainConfiguration.setConfigurations()
    domainConfiguration.storageFolder = storageFolder
    #changing default configuration
    domainConfiguration.TOTALNUMBEROFNODES = nodeNumber
    domainConfiguration.TOTALNUMBEROFAPPS = appNumber
    domainConfiguration.func_NETWORKGENERATION = "nx.barabasi_albert_graph(n="+str(domainConfiguration.TOTALNUMBEROFNODES)+", m=2)"
    

    domainConfiguration.setRandomState(randomSeeds)
    domainConfiguration.networkModel('n'+str(domainConfiguration.TOTALNUMBEROFNODES)+'-')
    domainConfiguration.appsGeneration()
    domainConfiguration.usersConnectionGeneration()
    
    
    
    
    Gdistances = deviceDistances(domainConfiguration.Gfdev)
    g_distances_with_cloud = deviceDistances(domainConfiguration.G) ## este tiene el cloud
    
    maxDistance = 0
    
    for i,v in Gdistances.items():
        for j,w in v.items():
            maxDistance = max(maxDistance,w)
    
    
    print("SI_CAMBIA_NETWORK:Inicio de los calculos sobre la estructura de la red....")
    time_net = time.time()
    GAstructure4partition = dendrogramCalculation(domainConfiguration.Gfdev)
    

    
    orderedCloserNodesInColony = oderNodesInColony(GAstructure4partition)
    print("SI_CAMBIA_NETWORK:Calculos sobre la red "+str(time.time()-time_net))
    allNodes = set(domainConfiguration.Gfdev.nodes)
    
    
    time_user = time.time()
    numUserService4Colonies = getNumUserService4Colonies(GAstructure4partition)

    orderedAppPopularity4Colonies, ordered_app_popularity_4colonies_list = orderAppsPopularityInColony(numUserService4Colonies)
    

    print("SI_CAMBIA_USUARIOS&APPS:Calculos sobre la cantidad de usuarios y popularidad de apps "+str(time.time()-time_user))
    
    
    
    
    experimentsData = list()
    
    
    
    
    print("OPT_GA:Inicio optimizacion GA")
    time_GA = time.time()
    
    
    
    print(random.random())
    
    
    pop = createPopulation()
    fastNonDominatedSort(pop)
    
    #calculateFitnessPop(pop)
    oneIterationData = dict()
    
    oneIterationData['min_allocation_time'] = list()
    oneIterationData['max_allocation_time'] = list()
    oneIterationData['min_latency'] = list()
    oneIterationData['max_latency'] = list()
    oneIterationData['min_total'] = list()
    
    
    oneIterationData['all_paretox'] = list()
    oneIterationData['all_paretoy'] =list()
    oneIterationData['all_nonparetox'] = list()
    oneIterationData['all_nonparetoy'] = list()
    
    
    oneIterationData['meanMaxX'] = list()
    oneIterationData['meanMaxY'] = list()
    
    oneIterationData['meanMinX'] = list()
    oneIterationData['meanMinY'] = list()
    
    oneIterationData['allParetoFrontsX'] = list()
    oneIterationData['allParetoFrontsY'] = list()
    
    
    
    
    for g in range(numberGenerations):
    
        ACTUAL_GENERATION = g
    
        SCATTER_X = []
        SCATTER_Y = []
    
        print("GEN:Inicio generacion ", ACTUAL_GENERATION)
        time_Gen = time.time()
        bothpops = newGeneration(pop=pop,repeat=repeatedSolutions)
        fastNonDominatedSort(bothpops)
    
        pop = splitPopsByDominance(bothpops)
        fastNonDominatedSort(pop)
    
        #print(len(pop['Col']))
        print("GEN:Generacion numero: "+str(g)+" "+str(time.time()-time_Gen))
        print(pop['fronts'][0])
        
        
        paretox=list()
        paretoy=list()
        nonparetox=list()
        nonparetoy=list()
        
            
            
        for idx,j in enumerate(pop['fronts']):
            for i in j:
                if idx==0:
                    paretox.append(pop['fitness'][i]['max_allocation_time'])
                    paretoy.append(pop['fitness'][i]['estimated_latency'])
                else:
                    nonparetox.append(pop['fitness'][i]['max_allocation_time'])
                    nonparetoy.append(pop['fitness'][i]['estimated_latency'])
        
        
        oneIterationData['all_paretox'].append(paretox)
        oneIterationData['all_paretoy'].append(paretoy)
        oneIterationData['all_nonparetox'].append(nonparetox)
        oneIterationData['all_nonparetoy'].append(nonparetoy)
        
        oneIterationData['meanMaxX'].append(max(paretox))
        oneIterationData['meanMaxY'].append(max(paretoy))
    
        oneIterationData['meanMinX'].append(min(paretox))
        oneIterationData['meanMinY'].append(min(paretoy))
    
    
            
        
        
        plt.scatter(nonparetox, nonparetoy)
        plt.scatter(paretox, paretoy)
        
        plt.title('Optimization points')
        plt.xlabel("Max allocation time")
        if ILP_METHOD:
            plt.ylabel("Free resources")
        else:
            plt.ylabel("Estimated latency")
    
        #plt.xlim(min_x, max_x)
        #plt.ylim(min_y, max_y)
    
        plt.savefig(storageFolder+"scatterPlot_GEN"+str(g)+".pdf",format='pdf')
        plt.close()
        
    
        # calcula minimos y maximos globales ??
        my_min,my_max = getMinMaxObjective('max_allocation_time')
        oneIterationData['min_allocation_time'].append(my_min)
        oneIterationData['max_allocation_time'].append(my_max)
        if ILP_METHOD:
            my_min,my_max = getMinMaxObjective('free_resources')
        else:
            my_min,my_max = getMinMaxObjective('estimated_latency')
        oneIterationData['min_latency'].append(my_min)
        oneIterationData['max_latency'].append(my_max)
        my_min,my_max = getMinMaxObjective('total')
        oneIterationData['min_total'].append(my_min)
    
        
        ALL_X_PLOT.append(SCATTER_X if SCATTER_X else [0])
        ALL_Y_PLOT.append(SCATTER_Y if SCATTER_Y else [0])
    
    
    
    
    controlCases = dict()
    
    
    
    #******************************************************************************************
    #   Obtaining control cases scenarios
    #******************************************************************************************
    controlCases['ot1c'],controlCases['rt1c']=getOnlyOneColony()
    sizeOfFixedColonies = 5
    controlCases['otCc'],controlCases['rtCc']=getCentralityAwareColony(sizeOfFixedColonies)
    #******************************************************************************************
    #   END Obtaining control cases scenarios
    #******************************************************************************************
    
    
    
    
    
    #******************************************************************************************
    #   Plots creation
    #******************************************************************************************
    
    
    
    
    
    #LAS X son los optimization times
    #las Y son los estimated execution (responses) times
    
    
    xlimit =max(sum(oneIterationData['meanMaxX'])/len(oneIterationData['meanMaxX']),controlCases['otCc'])
    ylimit =max(sum(oneIterationData['meanMaxY'])/len(oneIterationData['meanMaxY']),controlCases['rtCc'])
    
    
    xlimitmin =min(sum(oneIterationData['meanMinX'])/len(oneIterationData['meanMinX']),controlCases['otCc'])
    ylimitmin =min(sum(oneIterationData['meanMinY'])/len(oneIterationData['meanMinY']),controlCases['rtCc'])
    

    
    
    xlimit=xlimit*1.1
    ylimit=ylimit*1.1
    
    xlimitmin=xlimitmin*0.9
    ylimitmin=ylimitmin*0.9
    
    
    minX = min(oneIterationData['meanMinX'])
    minY = min(oneIterationData['meanMinY'])
    maxX = max(oneIterationData['meanMaxX'])
    maxY = max(oneIterationData['meanMaxY'])
    
    diffX = maxX-minX
    diffY = maxY-minY
    
    meanCloserTo00 =list()
    meanCloserTo00X = list()
    meanCloserTo00Y = list()
    
    hyperVolume = list()
    coverage1CGA = list()
    coverageFSGA = list()
    coverageGA1C = list()
    coverageGAFS = list()
    
    
    
    for i in range(len(oneIterationData['all_paretox'])):
        
        minDistance = float('inf')
        indxMin = -1
        
        paretoMaxX = -1.0
        paretoMaxY= -1.0
        paretoMinX = float('inf')
        paretoMinY = float('inf')
        
        SOLdominates1C = 0
        SOLdominatesFS = 0
        
        one1CdominatesSOL = 0
        FSdominatesSOL = 0
        
        print("Generation "+str(i))
        print("Pareto size " + str(len(oneIterationData['all_paretox'][i])))
        
        for j in range(len(oneIterationData['all_paretox'][i])):
            x_value = oneIterationData['all_paretox'][i][j]
            y_value = oneIterationData['all_paretoy'][i][j]
            
            
            
            
            if (controlCases['otCc'] <= x_value) and (controlCases['rtCc'] <= y_value):
                FSdominatesSOL+=1
                
            if (controlCases['ot1c'] <= x_value) and (controlCases['rt1c'] <= y_value):
                one1CdominatesSOL+=1
                
                
            if (x_value <= controlCases['otCc']) and (y_value <= controlCases['rtCc']):
                SOLdominatesFS=1
                
            if (x_value <= controlCases['ot1c']) and (y_value <= controlCases['rt1c']):
                SOLdominates1C=1
            
            
            x_value = (x_value-minY)/diffX
            y_value = (y_value-minY)/diffY
            
            paretoMinX = min(paretoMinX,x_value)
            paretoMinY = min(paretoMinY,y_value)
            
            paretoMaxX = min(paretoMaxX,x_value)
            paretoMaxY = min(paretoMaxY,y_value)
            
            
            distanceToCeroCero = math.sqrt(x_value**2 + y_value**2)
            if distanceToCeroCero < minDistance:
                minDistance = distanceToCeroCero
                indxMin = j
                
        meanCloserTo00X.append(oneIterationData['all_paretox'][i][indxMin])
        meanCloserTo00Y.append(oneIterationData['all_paretoy'][i][indxMin])
        meanCloserTo00.append(minDistance)
        
        value4HyperVolume = (float(paretoMaxX)-float(paretoMinX)) * (float(paretoMaxY)-float(paretoMinY))
        hyperVolume.append(value4HyperVolume)

        perc_dominance = float(float(FSdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
        coverageFSGA.append(perc_dominance)
        
        perc_dominance = float(float(one1CdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
        coverage1CGA.append(perc_dominance)
        
        coverageGA1C.append(SOLdominates1C)
        coverageGAFS.append(SOLdominatesFS)
        
        
        plt.xlim(xlimitmin,xlimit)
        plt.ylim(ylimitmin,ylimit)
    
        plt.scatter(oneIterationData['all_nonparetox'][i], oneIterationData['all_nonparetoy'][i])
        plt.scatter(oneIterationData['all_paretox'][i], oneIterationData['all_paretoy'][i])
        plt.scatter(controlCases['ot1c'],controlCases['rt1c'],marker='x',color='g')
        plt.scatter(controlCases['otCc'],controlCases['rtCc'],marker='x',color='r')
        plt.scatter(oneIterationData['all_paretox'][i][indxMin], oneIterationData['all_paretoy'][i][indxMin],marker='*',color='#000000')
        
        plt.title('Objective space')
        plt.xlabel("placement_time (ms)")
        if ILP_METHOD:
            plt.ylabel("Free resources")
        else:
            plt.ylabel("response_time (ms)")
    
    
        plt.savefig(storageFolder+"scaled_scatterPlot_GEN"+str(i)+".pdf",format='pdf')
        plt.close()
    
    
    
    finalHyperVolume.append(hyperVolume[-1])
    finalCoverageFSGA.append(coverageFSGA[-1])
    finalCoverage1CGA.append(coverage1CGA[-1])
    finalCoverageGAFS.append(coverageGAFS[-1])
    finalCoverageGA1C.append(coverageGA1C[-1])
    
    
    plt.plot(range(len(oneIterationData['meanMinX'])), oneIterationData['meanMinX'])
    plt.plot(range(len(oneIterationData['meanMaxX'])), oneIterationData['meanMaxX'])
    plt.plot(range(len(meanCloserTo00X)), meanCloserTo00X)
    
    plt.title('Evolution of the objective placement_time')
    plt.xlabel("Generation")
    plt.ylabel("placement_time (ms)")
    
    
    plt.savefig(storageFolder+"optimizationTime.pdf",format='pdf')
    plt.close()
    
    
    
    
    plt.plot(range(len(oneIterationData['meanMinY'])), oneIterationData['meanMinY'])
    plt.plot(range(len(oneIterationData['meanMaxY'])), oneIterationData['meanMaxY'])
    plt.plot(range(len(meanCloserTo00Y)), meanCloserTo00Y)


    
    plt.title('Evolution of the objective response_time')
    plt.xlabel("Generation")
    plt.ylabel("response_time (ms)")
    
    
    plt.savefig(storageFolder+"responseTime.pdf",format='pdf')
    plt.close()
    
    
    
    
    plt.plot(range(len(meanCloserTo00)), meanCloserTo00)
    
    plt.title('Evolution of the selected solution')
    plt.xlabel("Generation")
    plt.ylabel("Normalized fitness")
    
    
    plt.savefig(storageFolder+"selected.pdf",format='pdf')
    plt.close()
    
    
    
    radarLabels.append(str(nodeNumber)+"nodes\n"+str(appNumber)+"apps")
    fsColonyOptTime.append(controlCases['otCc'])
    oneColoyOptTime.append(controlCases['ot1c'])
    selectedFromParetoOptTime.append(meanCloserTo00X[-1])
    
    fsColonyNetTime.append(controlCases['rtCc'])
    oneColoyNetTime.append(controlCases['rt1c'])
    selectedFromParetoNetTime.append(meanCloserTo00Y[-1])
    
    


    
    plt.plot(range(len(hyperVolume)), hyperVolume)
    
    plt.title('Evolution of the S(GA)')
    plt.xlabel("Generation")
    plt.ylabel("S(GA)")
    
    
    plt.savefig(storageFolder+"hypervolume.pdf",format='pdf')
    plt.close()
    
    
    
    plt.plot(range(len(coverageFSGA)), coverageFSGA,label='C(fixed-size,GA)')
    plt.plot(range(len(coverage1CGA)), coverage1CGA,label='C(one-colony,GA)')
    plt.plot(range(len(coverageFSGA)), coverageGAFS,label='C(GA,fixed-size)')
    plt.plot(range(len(coverage1CGA)), coverageGA1C,label='C(GA,one-colony)')
    
    plt.title('Coverage evolution')
    plt.xlabel("Generation")
    plt.ylabel("coverage")
    
    plt.legend(loc="upper left")
    

    
    plt.savefig(storageFolder+"coverage.pdf",format='pdf')
    plt.close()
    



    
    
    #******************************************************************************************
    #   END Plots creation
    #******************************************************************************************
   
    oneIterationData['controlCases']=controlCases
    oneIterationData['GAstructure4partition']=GAstructure4partition
    oneIterationData['domainConfiguration']=domainConfiguration
    
    
    
    
    
    
    file = open(storageFolder+'resultdata.pickle', 'wb')
    pickle.dump(oneIterationData, file)
    file.close()


    
    radar = dict()
    radar['radarLabels']=radarLabels
    radar['fsColonyOptTime']=fsColonyOptTime
    radar['oneColoyOptTime']=oneColoyOptTime
    radar['selectedFromParetoOptTime']=selectedFromParetoOptTime
    radar['fsColonyNetTime']=fsColonyNetTime
    radar['oneColoyNetTime']=oneColoyNetTime
    radar['selectedFromParetoNetTime']=selectedFromParetoNetTime
    radar['finalHyperVolume']=finalHyperVolume
    radar['finalCoverageFSGA']=finalCoverageFSGA
    radar['finalCoverage1CGA']=finalCoverage1CGA
    radar['finalCoverageGAFS']=finalCoverageGAFS
    radar['finalCoverageGA1C']=finalCoverageGA1C

    file = open(storageFoldershort+'radarplot.pickle', 'wb')
    pickle.dump(radar, file)
    file.close()        

#******************************************************************************************
#   END Main loud execution experiments for different number of apps and nodes
#******************************************************************************************


radar = dict()
radar['radarLabels']=radarLabels
radar['fsColonyOptTime']=fsColonyOptTime
radar['oneColoyOptTime']=oneColoyOptTime
radar['selectedFromParetoOptTime']=selectedFromParetoOptTime
radar['fsColonyNetTime']=fsColonyNetTime
radar['oneColoyNetTime']=oneColoyNetTime
radar['selectedFromParetoNetTime']=selectedFromParetoNetTime
radar['finalHyperVolume']=finalHyperVolume
radar['finalCoverageFSGA']=finalCoverageFSGA
radar['finalCoverage1CGA']=finalCoverage1CGA
radar['finalCoverageGAFS']=finalCoverageGAFS
radar['finalCoverageGA1C']=finalCoverageGA1C


for i,v in enumerate(radar['radarLabels']):
    print(v+"  &  "+str(radar['finalHyperVolume'][i])+"  &  "+str(radar['finalCoverageFSGA'][i])+"  &  "+str(radar['finalCoverage1CGA'][i])+"  &  "+str(radar['finalCoverageGAFS'][i])+"  &  "+str(radar['finalCoverageGA1C'][i])+"\\\\ \midrule") 



file = open(storageFoldershort+'radarplot.pickle', 'wb')
pickle.dump(radar, file)
file.close()





with open(storageFoldershort+'radarplot.pickle', 'rb') as f:
    radar2 = pickle.load(f)
 

radarLabels=radar2['radarLabels']
fsColonyOptTime=radar2['fsColonyOptTime']
oneColoyOptTime=radar2['oneColoyOptTime']
selectedFromParetoOptTime=radar2['selectedFromParetoOptTime']
fsColonyNetTime=radar2['fsColonyNetTime']
oneColoyNetTime=radar2['oneColoyNetTime']
selectedFromParetoNetTime=radar2['selectedFromParetoNetTime']
finalHyperVolume=radar2['finalHyperVolume']
finalCoverageFSGA=radar2['finalCoverageFSGA']
finalCoverage1CGA=radar2['finalCoverage1CGA']
finalCoverageGAFS=radar2['finalCoverageGAFS']
finalCoverageGA1C=radar2['finalCoverageGA1C']


     
# Libraries
import matplotlib.pyplot as plt
import pandas as pd
from math import pi
 



my_palette = plt.cm.get_cmap("Set2", 4)    
 
# ------- PART 1: Create background
 
# number of variable
categories=radarLabels
N = len(categories)
 
# What will be the angle of each axis in the plot? (we divide the plot / number of variable)
angles = [n / float(N) * 2 * pi for n in range(N)]
angles += angles[:1]
 
# Initialise the spider plot
ax = plt.subplot(111, polar=True)
 
# If you want the first axis to be on top:
ax.set_theta_offset(pi / 2)
ax.set_theta_direction(-1)
 
# Draw one axe per variable + add labels
plt.xticks(angles[:-1], categories)
plt.yticks(fontsize=6)
plt.xticks(fontsize=8)


ax.tick_params(axis='x', which='major', pad=10)

 
 

# ------- PART 2: Add plots
 
# Plot each individual = each line of the data
# I don't make a loop, because plotting more than 3 groups makes the chart unreadable
 
# Ind1
ind1 = copy.copy(oneColoyOptTime)
ind1.append(oneColoyOptTime[0])
values=ind1
ax.plot(angles, values, linewidth=1, color=my_palette(0), linestyle='solid', label="one-colony")
ax.fill(angles, values, color=my_palette(0), alpha=0.4)
 
# Ind2
ind2 = copy.copy(fsColonyOptTime)
ind2.append(fsColonyOptTime[0])
values=ind2
ax.plot(angles, values, linewidth=1, color=my_palette(1), linestyle='solid', label="fixed-size")
ax.fill(angles, values, color=my_palette(1), alpha=0.4)


# Ind3
ind3 = copy.copy(selectedFromParetoOptTime)
ind3.append(selectedFromParetoOptTime[0])
values=ind3
ax.plot(angles, values, linewidth=1, color=my_palette(2), linestyle='solid', label="smallED-GA")
ax.fill(angles, values, color=my_palette(2), alpha=0.4)




plt.title('placement_time (ms)',y=1.2,fontweight="bold")
 
# Add legend


handles, labels = plt.gca().get_legend_handles_labels()
plt.legend([ plt.Rectangle((0, 0), 1, 1, fc=my_palette(i)) for i,handle in enumerate(handles)],
           [label for i,label in enumerate(labels)], 
           handlelength=0.8, handleheight=0.8,fontsize=6, loc='upper right', bbox_to_anchor=(0.1, 0.1))


plt.tight_layout()

# Show the graph
plt.savefig(storageFoldershort+"radarOptTime.pdf",format='pdf')
plt.close()




   
 
# ------- PART 1: Create background
 
# number of variable
categories=radarLabels
N = len(categories)
 
# What will be the angle of each axis in the plot? (we divide the plot / number of variable)
angles = [n / float(N) * 2 * pi for n in range(N)]
angles += angles[:1]
 
# Initialise the spider plot
ax = plt.subplot(111, polar=True)
 
# If you want the first axis to be on top:
ax.set_theta_offset(pi / 2)
ax.set_theta_direction(-1)
 
# Draw one axe per variable + add labels
plt.xticks(angles[:-1], categories)
plt.yticks(fontsize=6)
plt.xticks(fontsize=8)


ax.tick_params(axis='x', which='major', pad=10)



# ------- PART 2: Add plots
 
# Plot each individual = each line of the data
# I don't make a loop, because plotting more than 3 groups makes the chart unreadable
 
 
# Ind2
ind2 = copy.copy(fsColonyOptTime)
ind2.append(fsColonyOptTime[0])
values=ind2
ax.plot(angles, values, linewidth=1, color=my_palette(1), linestyle='solid', label="fixed-size")
ax.fill(angles, values, color=my_palette(1), alpha=0.4)


# Ind3
ind3 = copy.copy(selectedFromParetoOptTime)
ind3.append(selectedFromParetoOptTime[0])
values=ind3
ax.plot(angles, values, linewidth=1, color=my_palette(2), linestyle='solid', label="smallED-GA")
ax.fill(angles, values, color=my_palette(2), alpha=0.4)



plt.title('placement_time (ms)',y=1.2,fontweight="bold")
 
# Add legend


handles, labels = plt.gca().get_legend_handles_labels()
plt.legend([ plt.Rectangle((0, 0), 1, 1, fc=my_palette(i)) for i,handle in enumerate(handles)],
           [label for i,label in enumerate(labels)], 
           handlelength=0.8, handleheight=0.8, fontsize=6, loc='upper right', bbox_to_anchor=(0.1, 0.1))


plt.tight_layout()


# Show the graph
plt.savefig(storageFoldershort+"radarOptTime2.pdf",format='pdf')
plt.close()


    
 
# ------- PART 1: Create background
 
# number of variable
categories=radarLabels
N = len(categories)
 
# What will be the angle of each axis in the plot? (we divide the plot / number of variable)
angles = [n / float(N) * 2 * pi for n in range(N)]
angles += angles[:1]
 
# Initialise the spider plot
ax = plt.subplot(111, polar=True)
 
# If you want the first axis to be on top:
ax.set_theta_offset(pi / 2)
ax.set_theta_direction(-1)
 
# Draw one axe per variable + add labels
plt.xticks(angles[:-1], categories)
plt.yticks(fontsize=6)
plt.xticks(fontsize=8)


ax.tick_params(axis='x', which='major', pad=10)


 
# ------- PART 2: Add plots
 
# Plot each individual = each line of the data
# I don't make a loop, because plotting more than 3 groups makes the chart unreadable
 
# Ind1
ind1 = copy.copy(oneColoyNetTime)
ind1.append(oneColoyNetTime[0])
values=ind1
ax.plot(angles, values, linewidth=1, color=my_palette(0), linestyle='solid', label="one-colony")
ax.fill(angles, values, color=my_palette(0), alpha=0.4)
 
# Ind2
ind2 = copy.copy(fsColonyNetTime)
ind2.append(fsColonyNetTime[0])
values=ind2
ax.plot(angles, values, linewidth=1, color=my_palette(1), linestyle='solid', label="fixed-size")
ax.fill(angles, values, color=my_palette(1), alpha=0.4)


# Ind3
ind3 = copy.copy(selectedFromParetoNetTime)
ind3.append(selectedFromParetoNetTime[0])
values=ind3
ax.plot(angles, values, linewidth=1, color=my_palette(2), linestyle='solid', label="smallED-GA")
ax.fill(angles, values, color=my_palette(2), alpha=0.4)
 

plt.title('response_time (ms)',y=1.2,fontweight="bold")
 
# Add legend


handles, labels = plt.gca().get_legend_handles_labels()
plt.legend([ plt.Rectangle((0, 0), 1, 1, fc=my_palette(i)) for i,handle in enumerate(handles)],
           [label for i,label in enumerate(labels)], 
           handlelength=0.8, handleheight=0.8, fontsize=6, loc='upper right', bbox_to_anchor=(0.1, 0.1))


plt.tight_layout()


# Show the graph
plt.savefig(storageFoldershort+"radarNetTime.pdf",format='pdf')
plt.close()


     
 
# ------- PART 1: Create background
 
# number of variable
categories=radarLabels
N = len(categories)
 
# What will be the angle of each axis in the plot? (we divide the plot / number of variable)
angles = [n / float(N) * 2 * pi for n in range(N)]
angles += angles[:1]
 
# Initialise the spider plot
ax = plt.subplot(111, polar=True)
 
# If you want the first axis to be on top:
ax.set_theta_offset(pi / 2)
ax.set_theta_direction(-1)
 
# Draw one axe per variable + add labels
plt.xticks(angles[:-1], categories)
plt.yticks(fontsize=6)
plt.xticks(fontsize=8)


ax.tick_params(axis='x', which='major', pad=10)

 
 

# ------- PART 2: Add plots
 
# Plot each individual = each line of the data
# I don't make a loop, because plotting more than 3 groups makes the chart unreadable
 

 
# Ind2
ind2 = copy.copy(fsColonyNetTime)
ind2.append(fsColonyNetTime[0])
values=ind2
ax.plot(angles, values, linewidth=1, color=my_palette(1), linestyle='solid', label="fixed-size")
ax.fill(angles, values, color=my_palette(1), alpha=0.4)


# Ind3
ind3 = copy.copy(selectedFromParetoNetTime)
ind3.append(selectedFromParetoNetTime[0])
values=ind3
ax.plot(angles, values, linewidth=1, color=my_palette(2), linestyle='solid', label="smallED-GA")
ax.fill(angles, values, color=my_palette(2), alpha=0.4)
 


plt.title('response_time (ms)',y=1.2,fontweight="bold")
 
# Add legend


handles, labels = plt.gca().get_legend_handles_labels()
plt.legend([ plt.Rectangle((0, 0), 1, 1, fc=my_palette(i)) for i,handle in enumerate(handles)],
           [label for i,label in enumerate(labels)], 
           handlelength=0.8, handleheight=0.8, fontsize=6, loc='upper right', bbox_to_anchor=(0.1, 0.1))




# Show the graph
plt.savefig(storageFoldershort+"radarNetTime2.pdf",format='pdf')
plt.close()

       
       

     
# Libraries
import matplotlib.pyplot as plt
import pandas as pd
from math import pi
 
   


my_palette = plt.cm.get_cmap("Set2", 4)    
 
# ------- PART 1: Create background
 
# number of variable
categories=radarLabels
N = len(categories)
 
# What will be the angle of each axis in the plot? (we divide the plot / number of variable)
angles = [n / float(N) * 2 * pi for n in range(N)]
angles += angles[:1]
 
# Initialise the spider plot
ax = plt.subplot(111, polar=True)
 
# If you want the first axis to be on top:
ax.set_theta_offset(pi / 2)
ax.set_theta_direction(-1)
 
# Draw one axe per variable + add labels
plt.xticks(angles[:-1], categories)
plt.yticks(fontsize=6)
plt.xticks(fontsize=8)
plt.ylim(0,50)


ax.tick_params(axis='x', which='major', pad=10)

 


# ------- PART 2: Add plots
 
# Plot each individual = each line of the data
# I don't make a loop, because plotting more than 3 groups makes the chart unreadable
 
# Ind1
ind1 = copy.copy(oneColoyOptTime)
ind1.append(oneColoyOptTime[0])
values=ind1
ax.plot(angles, values, linewidth=1, color=my_palette(0), linestyle='solid',  label="one-colony")
ax.fill(angles, values, color=my_palette(0), alpha=0.4)
 
# Ind2
ind2 = copy.copy(fsColonyOptTime)
ind2.append(fsColonyOptTime[0])
values=ind2
ax.plot(angles, values, linewidth=1, color=my_palette(1), linestyle='solid',  label="fixed-size")
ax.fill(angles, values, color=my_palette(1), alpha=0.4)


# Ind3
ind3 = copy.copy(selectedFromParetoOptTime)
ind3.append(selectedFromParetoOptTime[0])
values=ind3
ax.plot(angles, values, linewidth=1, color=my_palette(2), linestyle='solid', label="smallED-GA")
ax.fill(angles, values, color=my_palette(2), alpha=0.4)




plt.title('placement_time (ms)',y=1.2,fontweight="bold")
 
# Add legend


handles, labels = plt.gca().get_legend_handles_labels()
plt.legend([ plt.Rectangle((0, 0), 1, 1, fc=my_palette(i)) for i,handle in enumerate(handles)],
           [label for i,label in enumerate(labels)], 
           handlelength=0.8, fontsize=6, handleheight=0.8, loc='upper right', bbox_to_anchor=(0.1, 0.1))


plt.tight_layout()

# Show the graph
plt.savefig(storageFoldershort+"radarOptTime3.pdf",format='pdf')
plt.close()







#******************************************************************************************
#   Generation of the plots of the solution space for the last generation of each experiment scenario
#******************************************************************************************



for oneExperiment in experiments2execute:
    appNumber = oneExperiment[0]
    nodeNumber = oneExperiment[1]

    storageFolder = storageFoldershort+str(nodeNumber)+"nodes"+str(appNumber)+"apps/"

    with open(storageFolder+'resultdata.pickle', 'rb') as f:
        oneIterationData = pickle.load(f)
    
    print(oneIterationData)            
    f.close()
    
    controlCases=oneIterationData['controlCases']
    
    alternativeFileName = storageFoldershort+'finalscatter/'+str(nodeNumber)+"nodes"+str(appNumber)+"apps.pdf"
    
    
    #******************************************************************************************
    #   Plots creation
    #******************************************************************************************
    
    
    
    
    
    #LAS X son los optimization times
    #las Y son los estimated execution (responses) times
    
    
    
    xlimit =max(sum(oneIterationData['meanMaxX'])/len(oneIterationData['meanMaxX']),controlCases['otCc'])
    ylimit =max(sum(oneIterationData['meanMaxY'])/len(oneIterationData['meanMaxY']),controlCases['rtCc'])
    
    xlimitmin =min(sum(oneIterationData['meanMinX'])/len(oneIterationData['meanMinX']),controlCases['otCc'])
    ylimitmin =min(sum(oneIterationData['meanMinY'])/len(oneIterationData['meanMinY']),controlCases['rtCc'])
    
    
    
    xlimit=xlimit*1.1
    ylimit=ylimit*1.1
    
    xlimitmin=xlimitmin*0.9
    ylimitmin=ylimitmin*0.9
    
    
    minX = min(oneIterationData['meanMinX'])
    minY = min(oneIterationData['meanMinY'])
    maxX = max(oneIterationData['meanMaxX'])
    maxY = max(oneIterationData['meanMaxY'])
    
    diffX = maxX-minX
    diffY = maxY-minY
    
    meanCloserTo00 =list()
    meanCloserTo00X = list()
    meanCloserTo00Y = list()
    
    hyperVolume = list()
    coverage1CGA = list()
    coverageFSGA = list()
    coverageGA1C = list()
    coverageGAFS = list()
    
    
    i = len(oneIterationData['all_paretox'])-1
        
    minDistance = float('inf')
    indxMin = -1
    
    paretoMaxX = -1.0
    paretoMaxY= -1.0
    paretoMinX = float('inf')
    paretoMinY = float('inf')
    
    SOLdominates1C = 0
    SOLdominatesFS = 0
    
    one1CdominatesSOL = 0
    FSdominatesSOL = 0
    
    print("Generation "+str(i))
    print("Pareto size " + str(len(oneIterationData['all_paretox'][i])))
    
    for j in range(len(oneIterationData['all_paretox'][i])):
        x_value = oneIterationData['all_paretox'][i][j]
        y_value = oneIterationData['all_paretoy'][i][j]
        
        
        
        
        if (controlCases['otCc'] <= x_value) and (controlCases['rtCc'] <= y_value):
            FSdominatesSOL+=1
            
        if (controlCases['ot1c'] <= x_value) and (controlCases['rt1c'] <= y_value):
            one1CdominatesSOL+=1
            
            
        if (x_value <= controlCases['otCc']) and (y_value <= controlCases['rtCc']):
            SOLdominatesFS=1
            
        if (x_value <= controlCases['ot1c']) and (y_value <= controlCases['rt1c']):
            SOLdominates1C=1
        
        
        
        x_value = (x_value-minY)/diffX
        y_value = (y_value-minY)/diffY
        
        paretoMinX = min(paretoMinX,x_value)
        paretoMinY = min(paretoMinY,y_value)
        
        paretoMaxX = min(paretoMaxX,x_value)
        paretoMaxY = min(paretoMaxY,y_value)
        
        
        distanceToCeroCero = math.sqrt(x_value**2 + y_value**2)
        if distanceToCeroCero < minDistance:
            minDistance = distanceToCeroCero
            indxMin = j
            
    meanCloserTo00X.append(oneIterationData['all_paretox'][i][indxMin])
    meanCloserTo00Y.append(oneIterationData['all_paretoy'][i][indxMin])
    meanCloserTo00.append(minDistance)
    
    value4HyperVolume = (float(paretoMaxX)-float(paretoMinX)) * (float(paretoMaxY)-float(paretoMinY))
    hyperVolume.append(value4HyperVolume)

    perc_dominance = float(float(FSdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
    coverageFSGA.append(perc_dominance)
    
    perc_dominance = float(float(one1CdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
    coverage1CGA.append(perc_dominance)
    
    coverageGA1C.append(SOLdominates1C)
    coverageGAFS.append(SOLdominatesFS)
 
    
    plt.text(0.9, 0.9, str(nodeNumber)+"nodes\n"+str(appNumber)+"apps", horizontalalignment='right',
     verticalalignment='center', transform=ax.transAxes,fontsize=12,fontweight="bold")
    
    plt.xlim(xlimitmin,xlimit)
    plt.ylim(ylimitmin,ylimit)

    plt.scatter(oneIterationData['all_nonparetox'][i], oneIterationData['all_nonparetoy'][i])
    plt.scatter(oneIterationData['all_paretox'][i], oneIterationData['all_paretoy'][i])
    plt.scatter(controlCases['ot1c'],controlCases['rt1c'],marker='x',color='g')
    plt.scatter(controlCases['otCc'],controlCases['rtCc'],marker='x',color='r')
    plt.scatter(oneIterationData['all_paretox'][i][indxMin], oneIterationData['all_paretoy'][i][indxMin],marker='*',color='#000000')
    
    plt.title('Objective space')
    plt.xlabel("placement_time (ms)")
    if ILP_METHOD:
        plt.ylabel("Free resources")
    else:
        plt.ylabel("response_time (ms)")


    plt.savefig(alternativeFileName,format='pdf')
    plt.close()




#******************************************************************************************
#   Calculation of the generation number where the pareto set of the GA dominates the two control solutions
#******************************************************************************************



for oneExperiment in experiments2execute:
    appNumber = oneExperiment[0]
    nodeNumber = oneExperiment[1]

    storageFolder = storageFoldershort+str(nodeNumber)+"nodes"+str(appNumber)+"apps/"

    with open(storageFolder+'resultdata.pickle', 'rb') as f:
        oneIterationData = pickle.load(f)
    
    f.close()
    
    controlCases=oneIterationData['controlCases']
    
    alternativeFileName = storageFoldershort+'finalscatter/'+str(nodeNumber)+"nodes"+str(appNumber)+"apps.pdf"
    
    
    smallestGenerationDominates = 1000000
        
    for i in range(numberGenerations):        
        #******************************************************************************************
        #   Plots creation
        #******************************************************************************************
        
        
        
        
        
        #LAS X son los optimization times
        #las Y son los estimated execution (responses) times
        
        
        
        xlimit =max(sum(oneIterationData['meanMaxX'])/len(oneIterationData['meanMaxX']),controlCases['otCc'])
        ylimit =max(sum(oneIterationData['meanMaxY'])/len(oneIterationData['meanMaxY']),controlCases['rtCc'])
        
        
        xlimitmin =min(sum(oneIterationData['meanMinX'])/len(oneIterationData['meanMinX']),controlCases['otCc'])
        ylimitmin =min(sum(oneIterationData['meanMinY'])/len(oneIterationData['meanMinY']),controlCases['rtCc'])
        

        
        
        xlimit=xlimit*1.1
        ylimit=ylimit*1.1
        
        xlimitmin=xlimitmin*0.9
        ylimitmin=ylimitmin*0.9
        
        
        minX = min(oneIterationData['meanMinX'])
        minY = min(oneIterationData['meanMinY'])
        maxX = max(oneIterationData['meanMaxX'])
        maxY = max(oneIterationData['meanMaxY'])
        
        diffX = maxX-minX
        diffY = maxY-minY
        
        meanCloserTo00 =list()
        meanCloserTo00X = list()
        meanCloserTo00Y = list()
        
        hyperVolume = list()
        coverage1CGA = list()
        coverageFSGA = list()
        coverageGA1C = list()
        coverageGAFS = list()
        
        
            
        minDistance = float('inf')
        indxMin = -1
        
        paretoMaxX = -1.0
        paretoMaxY= -1.0
        paretoMinX = float('inf')
        paretoMinY = float('inf')
        
        SOLdominates1C = 0
        SOLdominatesFS = 0
        
        one1CdominatesSOL = 0
        FSdominatesSOL = 0
        
        
        for j in range(len(oneIterationData['all_paretox'][i])):
            x_value = oneIterationData['all_paretox'][i][j]
            y_value = oneIterationData['all_paretoy'][i][j]
            
            
            
            
            if (controlCases['otCc'] <= x_value) and (controlCases['rtCc'] <= y_value):
                FSdominatesSOL+=1
                
            if (controlCases['ot1c'] <= x_value) and (controlCases['rt1c'] <= y_value):
                one1CdominatesSOL+=1
                
                
            if (x_value <= controlCases['otCc']) and (y_value <= controlCases['rtCc']):
                SOLdominatesFS=1
                
            if (x_value <= controlCases['ot1c']) and (y_value <= controlCases['rt1c']):
                SOLdominates1C=1
            
            
            
            x_value = (x_value-minY)/diffX
            y_value = (y_value-minY)/diffY
            
            paretoMinX = min(paretoMinX,x_value)
            paretoMinY = min(paretoMinY,y_value)
            
            paretoMaxX = min(paretoMaxX,x_value)
            paretoMaxY = min(paretoMaxY,y_value)
            
            
            distanceToCeroCero = math.sqrt(x_value**2 + y_value**2)
            if distanceToCeroCero < minDistance:
                minDistance = distanceToCeroCero
                indxMin = j
                
        meanCloserTo00X.append(oneIterationData['all_paretox'][i][indxMin])
        meanCloserTo00Y.append(oneIterationData['all_paretoy'][i][indxMin])
        meanCloserTo00.append(minDistance)
        
        value4HyperVolume = (float(paretoMaxX)-float(paretoMinX)) * (float(paretoMaxY)-float(paretoMinY))
        hyperVolume.append(value4HyperVolume)
    
        perc_dominanceFSGA = float(float(FSdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
        coverageFSGA.append(perc_dominanceFSGA)
        
        perc_dominance1CGA = float(float(one1CdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
        coverage1CGA.append(perc_dominance1CGA)
        
        
        if (SOLdominates1C==1) and (SOLdominatesFS==1):
            smallestGenerationDominates=min(smallestGenerationDominates,i+1)

            
        
        coverageGA1C.append(SOLdominates1C)
        coverageGAFS.append(SOLdominatesFS)
        
    


    print(oneExperiment)
    print(smallestGenerationDominates)
        
    
    
 
    


#******************************************************************************************
#   Generation of the objective space scatter plots for the generations of a given experiment scenario
#******************************************************************************************



oneExperiment = (40,200)
appNumber = oneExperiment[0]
nodeNumber = oneExperiment[1]

storageFolder = storageFoldershort+str(nodeNumber)+"nodes"+str(appNumber)+"apps/"

with open(storageFolder+'resultdata.pickle', 'rb') as f:
    oneIterationData = pickle.load(f)

f.close()

controlCases=oneIterationData['controlCases']



smallestGenerationDominates = 1000000
    
for i in range(numberGenerations):        
    #******************************************************************************************
    #   Plots creation
    #******************************************************************************************
    
    
    alternativeFileName = storageFoldershort+'finalscatter/'+str(nodeNumber)+"nodes"+str(appNumber)+"apps-gen"+str(i)+".pdf"
    
    
    
    #LAS X son los optimization times
    #las Y son los estimated execution (responses) times
    
    
    xlimit =max(sum(oneIterationData['meanMaxX'])/len(oneIterationData['meanMaxX']),controlCases['otCc'])
    ylimit =max(sum(oneIterationData['meanMaxY'])/len(oneIterationData['meanMaxY']),controlCases['rtCc'])
    
    
    xlimitmin =min(sum(oneIterationData['meanMinX'])/len(oneIterationData['meanMinX']),controlCases['otCc'])
    ylimitmin =min(sum(oneIterationData['meanMinY'])/len(oneIterationData['meanMinY']),controlCases['rtCc'])
    
   
    
    xlimit=xlimit*1.1
    ylimit=ylimit*1.1
    
    xlimitmin=xlimitmin*0.9
    ylimitmin=ylimitmin*0.9
    
    
    minX = min(oneIterationData['meanMinX'])
    minY = min(oneIterationData['meanMinY'])
    maxX = max(oneIterationData['meanMaxX'])
    maxY = max(oneIterationData['meanMaxY'])
    
    diffX = maxX-minX
    diffY = maxY-minY
    
    meanCloserTo00 =list()
    meanCloserTo00X = list()
    meanCloserTo00Y = list()
    
    hyperVolume = list()
    coverage1CGA = list()
    coverageFSGA = list()
    coverageGA1C = list()
    coverageGAFS = list()
    
    
        
    minDistance = float('inf')
    indxMin = -1
    
    paretoMaxX = -1.0
    paretoMaxY= -1.0
    paretoMinX = float('inf')
    paretoMinY = float('inf')
    
    SOLdominates1C = 0
    SOLdominatesFS = 0
    
    one1CdominatesSOL = 0
    FSdominatesSOL = 0
    
    
    for j in range(len(oneIterationData['all_paretox'][i])):
        x_value = oneIterationData['all_paretox'][i][j]
        y_value = oneIterationData['all_paretoy'][i][j]
        
        
        
        
        if (controlCases['otCc'] <= x_value) and (controlCases['rtCc'] <= y_value):
            FSdominatesSOL+=1
            
        if (controlCases['ot1c'] <= x_value) and (controlCases['rt1c'] <= y_value):
            one1CdominatesSOL+=1
            
            
        if (x_value <= controlCases['otCc']) and (y_value <= controlCases['rtCc']):
            SOLdominatesFS=1
            
        if (x_value <= controlCases['ot1c']) and (y_value <= controlCases['rt1c']):
            SOLdominates1C=1
        
        
        
        x_value = (x_value-minY)/diffX
        y_value = (y_value-minY)/diffY
        
        paretoMinX = min(paretoMinX,x_value)
        paretoMinY = min(paretoMinY,y_value)
        
        paretoMaxX = min(paretoMaxX,x_value)
        paretoMaxY = min(paretoMaxY,y_value)
        
        
        distanceToCeroCero = math.sqrt(x_value**2 + y_value**2)
        if distanceToCeroCero < minDistance:
            minDistance = distanceToCeroCero
            indxMin = j
            
   meanCloserTo00X.append(oneIterationData['all_paretox'][i][indxMin])
    meanCloserTo00Y.append(oneIterationData['all_paretoy'][i][indxMin])
    meanCloserTo00.append(minDistance)
    
    value4HyperVolume = (float(paretoMaxX)-float(paretoMinX)) * (float(paretoMaxY)-float(paretoMinY))
    hyperVolume.append(value4HyperVolume)

    perc_dominanceFSGA = float(float(FSdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
    coverageFSGA.append(perc_dominanceFSGA)
    
    perc_dominance1CGA = float(float(one1CdominatesSOL)/float(len(oneIterationData['all_paretox'][i])))
    coverage1CGA.append(perc_dominance1CGA)
    
    
    if (SOLdominates1C==1) and (SOLdominatesFS==1):
        smallestGenerationDominates=min(smallestGenerationDominates,i+1)

        
    
    coverageGA1C.append(SOLdominates1C)
    coverageGAFS.append(SOLdominatesFS)
    

    plt.text(0.95, 0.95, "Generation "+str(i+1), horizontalalignment='right',
     verticalalignment='center', transform=ax.transAxes,fontsize=12,fontweight="bold")
    
    plt.xlim(xlimitmin,xlimit)
    plt.ylim(ylimitmin,ylimit)

    plt.scatter(oneIterationData['all_nonparetox'][i], oneIterationData['all_nonparetoy'][i])
    plt.scatter(oneIterationData['all_paretox'][i], oneIterationData['all_paretoy'][i])
    plt.scatter(controlCases['ot1c'],controlCases['rt1c'],marker='x',color='g')
    plt.scatter(controlCases['otCc'],controlCases['rtCc'],marker='x',color='r')
    plt.scatter(oneIterationData['all_paretox'][i][indxMin], oneIterationData['all_paretoy'][i][indxMin],marker='*',color='#000000')
    
    plt.title('Objective space')
    plt.xlabel("placement_time (ms)")
    if ILP_METHOD:
        plt.ylabel("Free resources")
    else:
        plt.ylabel("response_time (ms)")



    plt.savefig(alternativeFileName,format='pdf')
    plt.close() 
        