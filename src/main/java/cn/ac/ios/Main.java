package cn.ac.ios;

import cn.ac.ios.Bean.ReDoSBean;
import cn.ac.ios.Utils.multithread.ITask;
import cn.ac.ios.Utils.multithread.MultiBaseBean;
import cn.ac.ios.Utils.multithread.MultiThreadUtils;
import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * 主程序入口
 *
 * @author pqc
 */
public class Main {

    private static final String HELP_FLAG = "-h";
    private static final String TIMEOUT_SETTING = "-t";
    private static final String ATTACK_MODEL = "-a";
    private static final String LANGUAGE = "-l";


    /* default settings */
    private static final int DEFAULT_TIMEOUT = 60;
    public static final String ATTACK_MODEL_SINGLE = "s";
    public static final String ATTACK_MODEL_MULTI = "m";
    public static final String DEFAULT_LANGUAGE = "java";

    private static HashMap<String, String> commandLineSettings;


    /**
     * TODO 待实现
     *
     * @param args
     */
    public static void main(String[] args) {
//        try {
//            String regexsmt = Translator.INSTANCE.translate("cvc4", "00[\\sabc\\S]*＆～(\\d+)");
//            System.out.println(regexsmt);
//        } catch (FormatNotAvailableException | TranslationException e) {
//            throw new RuntimeException(e);
//        }

        Logger.getGlobal().setLevel(Level.OFF);
        commandLineSettings = new HashMap<>();
        for (String arg : args) {
            if (arg.contains(HELP_FLAG)) {
                printUsage();
                System.exit(0);
            }
            if (arg.startsWith("-")) {
                if (arg.contains("=")) {
                    int settingLastIndex = arg.indexOf("=");
                    String settingName = arg.substring(0, settingLastIndex);
                    String settingValue = arg.substring(settingLastIndex + 1);
                    commandLineSettings.put(settingName, settingValue);
                }
            }
        }


//        String version = System.getProperty("java.version");
//        if (!(version.startsWith("1.8") || version.startsWith("1.7") || version.startsWith("1.6"))) {
//            System.out.println("Warning: The current Java version(" + version + ") is not support,please use Java(8)");
//            System.exit(0);
//        }


        System.out.println("please input regex ");
        Scanner scanner = new Scanner(System.in);
        String regex = scanner.nextLine();
        System.out.println("input:" + regex);

        getResult(regex);
    }


    public static void getResult(String regex) {
        int timeout = Integer.parseInt(commandLineSettings.getOrDefault(TIMEOUT_SETTING, String.valueOf(DEFAULT_TIMEOUT)));
        String model = commandLineSettings.getOrDefault(ATTACK_MODEL, ATTACK_MODEL_MULTI);
        String language = commandLineSettings.getOrDefault(LANGUAGE, DEFAULT_LANGUAGE);
        ArrayList<String> tasksData = new ArrayList<>();
        tasksData.add(regex);
        MultiThreadUtils<String, ReDoSBean> threadUtils = MultiThreadUtils.newInstance(1, timeout);
        MultiBaseBean<List<ReDoSBean>> multiBaseBean;
        if (tasksData == null || tasksData.isEmpty()) {
            multiBaseBean = new MultiBaseBean<>(null);
        } else {
            multiBaseBean = threadUtils.execute(tasksData, null, new ITask<String, ReDoSBean>() {
                @Override
                public ReDoSBean execute(String regex, Map<String, Integer> params) {
                    return (ReDoSMain.checkReDoS(regex, params.get("id")));
                }
            });
        }
        MultiThreadUtils<ReDoSBean, ReDoSBean> threadValidateUtils = MultiThreadUtils.newInstance(1, 0);
        MultiBaseBean<List<ReDoSBean>> validateBeans;
        validateBeans = threadValidateUtils.execute(multiBaseBean.getData(), null, new ITask<ReDoSBean, ReDoSBean>() {
            @Override
            public ReDoSBean execute(ReDoSBean bean, Map<String, Integer> params) {
                return (ReDoSMain.validateReDoS(bean, model,"java"));
            }
        });

        for (ReDoSBean bean : validateBeans.getData()) {
            if (bean.isReDoS()) {
                System.out.println("Vulnerable");
                for (int i = 0; i < bean.getAttackBeanList().size(); i++) {
                    if (bean.getAttackBeanList().get(i).isAttackSuccess()) {
                        System.out.println("---------------------------------------------------------------------------");
                        System.out.println("Attack String :" + bean.getAttackBeanList().get(i).getAttackStringFormat());
                        System.out.println("prefix :" + bean.getAttackBeanList().get(i).getPrefix().getValue());
                        System.out.println("prefix :" + bean.getAttackBeanList().get(i).getPrefix().getValue().toSmtLib());
                        System.out.println("infix :" + bean.getAttackBeanList().get(i).getInfix().getValue());
                        System.out.println("infix :" + bean.getAttackBeanList().get(i).getInfix().getValue().toSmtLib());
                        System.out.println("suffix :" + bean.getAttackBeanList().get(i).getSuffix().getValue());
                        System.out.println("suffix :" + bean.getAttackBeanList().get(i).getSuffix().getValue().toSmtLib());
                        String smtlib = "(set-logic QF_SLIA)\n" +
                                        "(declare-const result String)\n" +
                                        "(declare-const attack String)\n" +
                                        "(declare-const prefix RegLan)\n" +
                                        "(declare-const infix RegLan)\n" +
                                        "(declare-const postfix RegLan)\n" +
                                        "(declare-const postfixs String)\n" +
                                        "\n" +
                                        "(assert (str.in.re attack (re.++ prefix ((_ re.loop "+bean.getAttackBeanList().get(i).getRepeatTimes()+" "+bean.getAttackBeanList().get(i).getRepeatTimes()+") infix) postfix)))\n" +
                                        "(assert (= prefix \n" +
                                        "    "+ ((bean.getAttackBeanList().get(i).getPrefix().getValue().toSmtLib().isEmpty())?"(str.to_re \"\")":bean.getAttackBeanList().get(i).getPrefix().getValue().toSmtLib()) +"\n" +
                                        "))\n" +
                                        "(assert (= infix \n" +
                                        "        "+ ((bean.getAttackBeanList().get(i).getInfix().getValue().toSmtLib().isEmpty()?"(str.to_re \"\")":bean.getAttackBeanList().get(i).getInfix().getValue().toSmtLib())) + "\n" +
                                        "))\n" +
                                        "(assert (= postfix \n" +
                                        "        "+ ((bean.getAttackBeanList().get(i).getSuffix().getValue().toSmtLib().isEmpty()?"(str.to_re \"\")":bean.getAttackBeanList().get(i).getSuffix().getValue().toSmtLib())) + "\n" +
                                        "))\n" +
                                        "(assert (str.in.re postfixs postfix))\n" +
                                        "(assert (>= (str.len postfixs) 1))\n" +
                                        "(assert (= result (str.++ attack postfixs)))\n" +
                                        "(check-sat)\n" +
                                        "(get-model)";
                    System.out.println("\nSMTLIB File:\n" + smtlib.replace("str.in.re", "str.in_re")
                            .replace("str.to.re","str.to_re")
                            .replace("(re.range \"\\x30\" \"\\x39\")", "(re.range \"0\" \"9\")")
                    );
                    }
                }
            } else {
                System.out.println("Safe");
            }
        }

        System.exit(0); // 新增
    }


    private static void printUsage() {
        System.out.println("usage: type the command \"java -jar lcp.jar\", Press enter");
        System.out.println("       then type your regex");
        System.out.println("       (optional)-t:  set the timeout to d seconds for check phase. If d <= 0, timeout is disabled. default is 60s;");
        System.out.println("       (optional)-a:  attack model: s (for vulnerable only), M (for validating all attack strings). default is s;");
//        System.out.println("\t (optional)-l:  programming language environment which used for regex，default in Java");
    }
}
