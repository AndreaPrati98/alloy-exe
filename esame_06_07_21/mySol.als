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

////////////////////////////////////////////////////////////////

pred show{
    some d:Device |
        #(d.hostedSwModules) > 0
}

run show for 6 but 6 int