sig SwModule{
    auth: Author,
    suppPack: PackagingTech
}

sig Author{}
abstract sig PackagingTech{}
one sig JAR,APK,DebPack,DocImg extends PackagingTech{}

sig Device{
    location: Location,
    packCanHandle: some PackagingTech,
    hostedSwModules: set SwModule
}

sig Location{}

sig Configuration{
    listOfDev: set Device,
    deployableModules: set SwModule
}

// the hostedSwModules on a device have to support the PackaginTech
// that is among the PackaginTech that the device can handle 
fact packConstraint {
    all d: Device |
        d.hostedSwModules.suppPack in d.packCanHandle      
}

// the swModule pack constraint
fact configSwModuleConstr{
    all c: Configuration |
        #(c.listOfDev.packCanHandle & c.deployableModules.suppPack) > 0
}

/*
    Define an Alloy function that returns, given a system configuration and a software module, the set of
    devices which host that module in that configuration.
*/
fun getDevCanHostSwMod [config: Configuration, swMod: SwModule] : set Device {
    let res = {d:Device | d in config.listOfDev and swMod in d.hostedSwModules}|
        res
}

/*
    Formalize in Alloy the behavior of an operation that takes as input a system configuration, a software
    module, and a device of the system, and deploys the module on the device; that is, if the module is not
    yet deployed on the device, the operation adds it to the list of modules that can be deployed
*/
pred deployOnDev[c0, c1 : Configuration, swMod: SwModule, d0: Device]{
    // Per-conditions
    d0 in c0.listOfDev // because there is written "dev of the sys"
    swMod.suppPack in d0.packCanHandle // the sw module has to support the pack tech that the dev can handle

    // Post-conditions
    c1.deployableModules = c0.deployableModules + swMod // the config at time 1 is like at time zero plus the new sw mdo
    // here we write that in the new config there is one or more devices
    // with the same caracteristics of before but with the the new sw mod
    some d1: Device |
        d1.location = d0.location and
        d1.packCanHandle = d0.packCanHandle and
        d1.hostedSwModules = d0.hostedSwModules + swMod and
        c1.listOfDev = c0.listOfDev - d0 + d1

}

////////////////////////////////////////////////////////////////

pred show{
    some d:Device |
        #(d.hostedSwModules) > 0
}

run show for 6 but 6 int