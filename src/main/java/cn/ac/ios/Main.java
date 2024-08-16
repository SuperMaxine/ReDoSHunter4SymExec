package cn.ac.ios;

import cn.ac.ios.Bean.ReDoSBean;
import cn.ac.ios.Utils.multithread.ITask;
import cn.ac.ios.Utils.multithread.MultiBaseBean;
import cn.ac.ios.Utils.multithread.MultiThreadUtils;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

import java.nio.file.Paths;
import java.nio.file.LinkOption;

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


       // try {
       //     String regexsmt = Translator.INSTANCE.translate("cvc4", "\\n");
       //     System.out.println(regexsmt);
       // } catch (FormatNotAvailableException | TranslationException e) {
       //     throw new RuntimeException(e);
       // }
       //
       //  return;

        getResult(0, "(a*)*.(\\w*)*");
    }


    public static void getResult(int regexId, String regex) {
        int timeout = Integer.parseInt(commandLineSettings.getOrDefault(TIMEOUT_SETTING, String.valueOf(DEFAULT_TIMEOUT)));
        // String model = commandLineSettings.getOrDefault(ATTACK_MODEL, ATTACK_MODEL_MULTI);
        String model = commandLineSettings.getOrDefault(ATTACK_MODEL, ATTACK_MODEL_SINGLE);
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
                return (ReDoSMain.validateReDoS(bean, model, language));
            }
        });

        // 如果output/文件夹不存在，则创建
        String outputDir = "output";
        if (!Files.exists(Paths.get(outputDir), LinkOption.NOFOLLOW_LINKS)) {
            try {
                // 创建目录，包括任何必需但不存在的父目录
                Files.createDirectories(Paths.get(outputDir));
                System.out.println("目录已创建: " + outputDir);
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else {
            System.out.println("目录已存在: " + outputDir);
        }

        for (ReDoSBean bean : validateBeans.getData()) {
            if (bean.isReDoS()) {
                System.out.println("Vulnerable");
                for (int i = 0; i < bean.getAttackBeanList().size(); i++) {
                    if (bean.getAttackBeanList().get(i).isAttackSuccess()) {
                        System.out.println("---------------------------------------------------------------------------");
                        try {
                            int validateId = validateBeans.getData().indexOf(bean);
                            int attackId = i;


                            String smtOfPrefix = bean.getAttackBeanList().get(i).getPrefix().getValue().toSmtLib();
                            String smtOfInfix = bean.getAttackBeanList().get(i).getInfix().getValue().toSmtLib();
                            String smtOfSuffix = bean.getAttackBeanList().get(i).getSuffix().getValue().toSmtLib();

                            int SMTCount = 0;

                            String smtlib = "(set-logic QF_SLIA)\n" +
                                    "(declare-const result String)\n" +
                                    "(declare-const attack String)\n" +
                                    "(declare-const prefix RegLan)\n" +
                                    "(declare-const infix RegLan)\n" +
                                    "(declare-const postfix RegLan)\n" +
                                    "(declare-const postfixs String)\n" +
                                    "\n" +
                                    "(assert (str.in.re attack (re.++ prefix ((_ re.loop " + bean.getAttackBeanList().get(i).getRepeatTimes() + " " + bean.getAttackBeanList().get(i).getRepeatTimes() + ") infix) postfix)))\n" +
                                    "(assert (= prefix \n" +
                                    "    " + ((smtOfPrefix.isEmpty()) ? "(str.to_re \"\")" : smtOfPrefix) + "\n" +
                                    "))\n" +
                                    "(assert (= infix \n" +
                                    "        " + ((smtOfInfix.isEmpty() ? "(str.to_re \"\")" : smtOfInfix)) + "\n" +
                                    "))\n" +
                                    "(assert (= postfix \n" +
                                    "        " + ((smtOfSuffix.isEmpty() ? "(str.to_re \"\")" : smtOfSuffix)) + "\n" +
                                    "))\n" +
                                    "(assert (str.in.re postfixs postfix))\n" +
                                    "(assert (>= (str.len postfixs) 1))\n" +
                                    "(assert (= result (str.++ attack postfixs)))\n" +
                                    "(check-sat)\n" +
                                    "(get-model)";


                            String smtlibFile = outputDir + "/" + regexId + "_" + validateId + "_" + attackId + "_" + SMTCount + ".smt2";
                            //写入smtlib文件
                            try {
                                Files.write(Paths.get(smtlibFile), smtlib.getBytes(StandardCharsets.UTF_8));
                                System.out.println("SMTLIB文件已写入: " + smtlibFile);
                            } catch (IOException e) {
                                e.printStackTrace();
                            }
                            // 写入调试信息
                            try {
                                Files.write(Paths.get(smtlibFile.replace("smt2","log")),
                                        Collections.singleton("prefix:\n" + bean.getAttackBeanList().get(i).getPrefix().getValue().toString() + "\n" +
                                                "infix:\n" + bean.getAttackBeanList().get(i).getInfix().getValue().toString() + "\n" +
                                                "suffix:\n" + bean.getAttackBeanList().get(i).getSuffix().getValue().toString() + "\n" +
                                                "repeatTimes:\n" + bean.getAttackBeanList().get(i).getRepeatTimes() + "\n" +
                                                "attackSuccess:\n" + bean.getAttackBeanList().get(i).isAttackSuccess() + "\n" +
                                                "attackString:\n" + bean.getAttackBeanList().get(i).getAttackString() + "\n")
                                        , StandardCharsets.UTF_8);
                                System.out.println("SMTLIB文件已写入: " + smtlibFile);
                            } catch (IOException e) {
                                e.printStackTrace();
                            }

                        } catch (Exception e) {
                            e.printStackTrace();
                        }
                    }
                }
            } else {
                System.out.println("Safe");
            }
        }

//        System.exit(0); // 新增
    }


    private static void printUsage() {
        System.out.println("usage: type the command \"java -jar lcp.jar\", Press enter");
        System.out.println("       then type your regex");
        System.out.println("       (optional)-t:  set the timeout to d seconds for check phase. If d <= 0, timeout is disabled. default is 60s;");
        System.out.println("       (optional)-a:  attack model: s (for vulnerable only), M (for validating all attack strings). default is s;");
//        System.out.println("\t (optional)-l:  programming language environment which used for regex，default in Java");
    }
}
