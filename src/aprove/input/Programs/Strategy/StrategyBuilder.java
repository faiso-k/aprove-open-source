package aprove.input.Programs.Strategy;

import java.util.*;

import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

public class StrategyBuilder implements DeclarationVisitor {
    private RawModule module;
    private Map<String, UserStrategy> strategies = new LinkedHashMap<String, UserStrategy>();
    private Map<String, NameDefinition> managerInfo = new LinkedHashMap<String, NameDefinition>();

    public StrategyBuilder(RawModule module) {
        this.module = module;
        this.build();
    }

    public Map<String, UserStrategy> getStrategies() {
        return this.strategies;
    }

    public Map<String, NameDefinition> getManagerInfo() {
        return this.managerInfo;
    }

    public StrategyProgram buildProgram() {
        return new StrategyProgram(this.strategies, this.managerInfo);
    }

    public StrategyProgram buildProgramWithDefaults(StrategyProgram defaults) {
        return new StrategyProgram(defaults, this.strategies, this.managerInfo);
    }

    private void build() {
        for (Declaration decl : this.module.getNamespace()) {
            decl.accept(this);
        }
    }

    @Override
    public void visit(ClassDeclaration decl) {
        NameDefinition def = new NameDefinition(decl.classname, StrategyBuilder.freeze(decl.defaults));
        this.managerInfo.put(decl.name, def);
    }

    @Override
    public void visit(LetDeclaration decl) {
        this.strategies.put(decl.name, StrategyBuilder.exprToUser(decl.body));
    }

    public static UserStrategy exprToUser(StrategyExpression body) {
        return body.accept(ExpressionToUserStrategy.INSTANCE);
    }

    public static FrozenParameters freeze(Parameters defaults) {
        return ValueToParamValue.freeze(defaults);
    }

    public static ParamValue freeze(Value value) {
        return value.accept(ValueToParamValue.INSTANCE);
    }
}
